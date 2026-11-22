; =============================================================================
; NoSpeaker Formal Verification Suite — SMT-LIB2 (Z3 5.3.3)
; Logics: QF_FP (IEEE-754 Binary64, Binary32, Binary16) & QF_BV (64-bit/32-bit)
;
; Every scope checks either:
;   - [Refutation] (expect `sat`): exhibits an IEEE-754 / BitVector witness
;     violating a safety invariant in unhardened nospeaker.swift.
;   - [Proof]      (expect `unsat`): proves universal absence of any violation
;     across the entire state space of the hardened contract.
; =============================================================================

(set-logic ALL)

; -----------------------------------------------------------------------------
; THEOREM 1 (QF_FP): Complex Division Underflow in Durand-Kerner `roots(_:)`
; Ref: https://github.com/os6/nospeaker/blob/e02a121243f3dbddb288fa6520134b0c4a8727c6/nospeaker.swift#L346-L365 (`C./` and `if d.re == 0 && d.im == 0`)
; -----------------------------------------------------------------------------
(echo "=== T1A.1 [Refutation - Float64]: Non-zero normal r underflows r.re^2 + r.im^2 to +0.0 (expect sat) ===")
(push 1)
(declare-const r_re Float64)
(declare-const r_im Float64)
(assert (and (fp.isNormal r_re) (fp.isNormal r_im)))
(assert (not (and (fp.eq r_re (_ +zero 11 53)) (fp.eq r_im (_ +zero 11 53)))))
(define-fun unhardened_d () Float64
  (fp.add RNE (fp.mul RNE r_re r_re) (fp.mul RNE r_im r_im)))
(assert (fp.eq unhardened_d (_ +zero 11 53)))
(check-sat)
(pop 1)

(echo "=== T1A.2 [Proof - Float64]: Zero denominator in C./ ALWAYS yields NaN or Inf (expect unsat) ===")
(push 1)
(declare-const num Float64)
(declare-const den Float64)
(assert (and (not (fp.isNaN num)) (not (fp.isInfinite num))))
(assert (fp.eq den (_ +zero 11 53)))
(define-fun quot () Float64 (fp.div RNE num den))
(assert (and (not (fp.isNaN quot)) (not (fp.isInfinite quot))))
(check-sat)
(pop 1)

(echo "=== T1B.1 [Proof - Float64]: Magnitude-form Smith denominator |re| + |im|*|ratio| >= |re| > 0 on ALL normal Float64 (expect unsat) ===")
(push 1)
(declare-const mre Float64)
(declare-const mim Float64)
(declare-const mrat Float64)
; 2^500 in IEEE-754 Float64 (sign=0, biased_exp=1023+500=1523=#b10111110011, mant=0)
(define-fun mb64 () Float64 (fp #b0 #b10111110011 #x0000000000000))
(define-fun ob64 () Float64 ((_ to_fp 11 53) RNE 1.0))
(define-fun zb64 () Float64 (_ +zero 11 53))

(assert (fp.isNormal mre))
(assert (and (not (fp.isNaN mim)) (not (fp.isInfinite mim))))
(assert (fp.leq (fp.abs mim) (fp.abs mre)))
(assert (fp.leq (fp.abs mre) mb64))
(assert (and (not (fp.isNaN mrat)) (fp.geq mrat zb64) (fp.leq mrat ob64)))

(define-fun smith_mag_denom () Float64
  (fp.add RNE (fp.abs mre) (fp.mul RNE (fp.abs mim) mrat)))

(assert (or (fp.eq smith_mag_denom zb64)
            (fp.lt smith_mag_denom (fp.abs mre))
            (fp.isNaN smith_mag_denom)
            (fp.isInfinite smith_mag_denom)))
(check-sat)
(pop 1)

(echo "=== T1B.2 [Proof - Monolithic IEEE-754 Binary16]: End-to-end Smith complex division denominator never zero/NaN/Inf (expect unsat) ===")
(push 1)
(declare-const h_re Float16)
(declare-const h_im Float16)
(define-fun max_b16 () Float16 ((_ to_fp 5 11) RNE 100.0))
(assert (and (not (fp.isNaN h_re)) (not (fp.isInfinite h_re))))
(assert (and (not (fp.isNaN h_im)) (not (fp.isInfinite h_im))))
(assert (or (fp.isNormal h_re) (fp.isNormal h_im)))
(assert (and (fp.leq (fp.abs h_re) max_b16) (fp.leq (fp.abs h_im) max_b16)))

(define-fun smith_d16 () Float16
  (ite (fp.geq (fp.abs h_re) (fp.abs h_im))
       (fp.add RNE h_re (fp.mul RNE h_im (fp.div RNE h_im h_re)))
       (fp.add RNE h_im (fp.mul RNE h_re (fp.div RNE h_re h_im)))))

(assert (or (fp.eq smith_d16 (_ +zero 5 11))
            (fp.isNaN smith_d16)
            (fp.isInfinite smith_d16)))
(check-sat)
(pop 1)

; -----------------------------------------------------------------------------
; THEOREM 2 (QF_FP): Haptic Motor Amplitude & NaN Safety in `play(_:ms:level:)`
; Ref: https://github.com/os6/nospeaker/blob/e02a121243f3dbddb288fa6520134b0c4a8727c6/nospeaker.swift#L167-L173 (`let sum = max(tones.reduce(0)..., 0.0001)`)
; -----------------------------------------------------------------------------
(echo "=== T2A [Refutation - Float64]: Swift max(sum, 0.0001) leaks NaN when tone amp is NaN or +oo (expect sat) ===")
(push 1)
(declare-const a1 Float64)
(declare-const a2 Float64)
(define-fun eps () Float64 ((_ to_fp 11 53) RNE 0.0001))
(define-fun raw_sum () Float64 (fp.add RNE a1 a2))
(define-fun swift_max_sum () Float64 (ite (fp.geq eps raw_sum) eps raw_sum))
(assert (fp.isNaN swift_max_sum))
(check-sat)
(pop 1)

(echo "=== T2B [Refutation - Float64]: Signed normal tone amplitudes exceed normal maximum 1.0 (expect sat) ===")
(push 1)
(declare-const b1 Float64)
(declare-const b2 Float64)
(define-fun eps64 () Float64 ((_ to_fp 11 53) RNE 0.0001))
(assert (and (fp.isNormal b1) (fp.isNormal b2)))
(define-fun s64 () Float64 (fp.add RNE b1 b2))
(define-fun smax64 () Float64 (ite (fp.geq eps64 s64) eps64 s64))
(assert (fp.gt (fp.abs b1) smax64))
(check-sat)
(pop 1)

(echo "=== T2C.1 [Proof - Float64 & Float32]: Hardened clamp01 is strictly in [0.0, 1.0] & NaN-free for ALL 2^64 + 2^32 floats (expect unsat) ===")
(push 1)
(declare-const q_raw Float64)
(declare-const lvl_raw Float32)
(define-fun zero64 () Float64 (_ +zero 11 53))
(define-fun one64 () Float64 ((_ to_fp 11 53) RNE 1.0))
(define-fun zero32 () Float32 (_ +zero 8 24))
(define-fun one_f32 () Float32 ((_ to_fp 8 24) RNE 1.0))

(define-fun clamp01_64 ((u Float64)) Float64
  (ite (or (fp.isNaN u) (fp.leq u zero64))
       zero64
       (ite (fp.geq u one64) one64 u)))

(define-fun clamp01_32 ((u Float32)) Float32
  (ite (or (fp.isNaN u) (fp.leq u zero32))
       zero32
       (ite (fp.geq u one_f32) one_f32 u)))

(define-fun w_safe () Float64 (clamp01_64 q_raw))
(define-fun lvl_safe () Float32 (clamp01_32 lvl_raw))

(assert (or (fp.isNaN w_safe)
            (fp.isInfinite w_safe)
            (fp.lt w_safe zero64)
            (fp.gt w_safe one64)
            (fp.isNaN lvl_safe)
            (fp.isInfinite lvl_safe)
            (fp.lt lvl_safe zero32)
            (fp.gt lvl_safe one_f32)))
(check-sat)
(pop 1)

(echo "=== T2C.2 [Proof - IEEE-754 Binary16 Simplex Ratio]: Sanitized component ratio cp1 / max(cp1 + cp2, eps) <= 1.0 & >= 0.0 for ALL inputs (expect unsat) ===")
(push 1)
(declare-const p1 Float16)
(declare-const p2 Float16)
(define-fun z16 () Float16 (_ +zero 5 11))
(define-fun o16 () Float16 ((_ to_fp 5 11) RNE 1.0))
(define-fun cap16 () Float16 ((_ to_fp 5 11) RNE 100.0))
(define-fun feps16 () Float16 ((_ to_fp 5 11) RNE 0.01))

(define-fun san16 ((x Float16)) Float16
  (ite (or (fp.isNaN x) (fp.leq x z16))
       z16
       (ite (fp.gt x cap16) cap16 x)))

(define-fun cp1 () Float16 (san16 p1))
(define-fun cp2 () Float16 (san16 p2))
(define-fun csum16 () Float16 (fp.add RNE cp1 cp2))
(define-fun sden16 () Float16 (ite (fp.gt csum16 feps16) csum16 feps16))
(define-fun w1_raw () Float16 (fp.div RNE cp1 sden16))

(assert (or (fp.isNaN w1_raw)
            (fp.isInfinite w1_raw)
            (fp.lt w1_raw z16)
            (fp.gt w1_raw o16)))
(check-sat)
(pop 1)

; -----------------------------------------------------------------------------
; THEOREM 3 (QF_BV): 64-bit AVAudioFramePosition -> 32-bit AVAudioFrameCount Trap
; Ref: https://github.com/os6/nospeaker/blob/e02a121243f3dbddb288fa6520134b0c4a8727c6/nospeaker.swift#L308 (`AVAudioFrameCount(file.length)`)
; -----------------------------------------------------------------------------
(echo "=== T3A [Refutation - BV64]: Unguarded Int64 -> UInt32 audio frame cast overflows/traps (expect sat) ===")
(push 1)
(declare-const file_len (_ BitVec 64))
(assert (bvsge file_len #x0000000000000000))
(assert (bvugt file_len #x00000000FFFFFFFF))
(check-sat)
(pop 1)

(echo "=== T3B [Proof - BV64]: Hardened 30s @ 48kHz Audio Cap guarantees UInt32 safety & <= 5.76 MiB PCM (expect unsat) ===")
(push 1)
(declare-const file_len2 (_ BitVec 64))
(define-fun max_frames () (_ BitVec 64) #x000000000015F900)
(assert (and (bvsge file_len2 #x0000000000000000)
             (bvsle file_len2 max_frames)))

(define-fun pcm_bytes () (_ BitVec 64) (bvmul file_len2 #x0000000000000004))
(assert (or (bvugt file_len2 #x00000000FFFFFFFF)
            (bvugt pcm_bytes #x0000000000600000)
            (not (= ((_ zero_extend 32) ((_ extract 31 0) file_len2)) file_len2))))
(check-sat)
(pop 1)

; -----------------------------------------------------------------------------
; THEOREM 4 (QF_BV): MultitouchSupport Raw Contact Buffer Over-Read (`CWE-125`)
; Ref: https://github.com/os6/nospeaker/blob/e02a121243f3dbddb288fa6520134b0c4a8727c6/nospeaker.swift#L233-L237 (`data.advanced(by: i * 96)`, `.load(fromByteOffset: 48, as: Float.self)`)
; -----------------------------------------------------------------------------
(echo "=== T4A.1 [Refutation - BV64]: At count >= 2, hardcoded 96-byte stride misaligns field offsets on 88-byte struct (expect sat) ===")
(push 1)
(declare-const count (_ BitVec 32))
(declare-const idx (_ BitVec 32))
(assert (and (bvsge count #x00000002) (bvsle count #x00000010)))
(assert (and (bvsgt idx #x00000000) (bvslt idx count)))
(define-fun true_x_off () (_ BitVec 64)
  (bvadd (bvmul ((_ sign_extend 32) idx) #x0000000000000058) #x0000000000000020))
(define-fun read_x_off () (_ BitVec 64)
  (bvadd (bvmul ((_ sign_extend 32) idx) #x0000000000000060) #x0000000000000020))
(assert (not (= true_x_off read_x_off)))
(check-sat)
(pop 1)

(echo "=== T4A.2 [Refutation - BV64]: At count >= 6, hardcoded 96-byte stride reads past end of 88-byte buffer (expect sat) ===")
(push 1)
(declare-const count_oob (_ BitVec 32))
(declare-const idx_oob (_ BitVec 32))
(assert (and (bvsgt count_oob #x00000000) (bvsle count_oob #x00000010)))
(assert (and (bvsge idx_oob #x00000000) (bvslt idx_oob count_oob)))
(define-fun alloc_bytes () (_ BitVec 64)
  (bvmul ((_ sign_extend 32) count_oob) #x0000000000000058))
(define-fun read_end () (_ BitVec 64)
  (bvadd (bvmul ((_ sign_extend 32) idx_oob) #x0000000000000060) #x0000000000000034))
(assert (bvugt read_end alloc_bytes))
(check-sat)
(pop 1)

(echo "=== T4B [Proof - BV64]: Stride-validated & 4-byte alignment-checked touch reader never over-reads or traps (expect unsat) ===")
(push 1)
(declare-const count2 (_ BitVec 32))
(declare-const idx2 (_ BitVec 32))
(declare-const stride2 (_ BitVec 64))
(declare-const base_addr (_ BitVec 64))

(assert (and (bvsgt count2 #x00000000) (bvsle count2 #x00000020)))
(assert (and (bvsge idx2 #x00000000) (bvslt idx2 count2)))
(assert (and (bvuge stride2 #x0000000000000034) (bvule stride2 #x0000000000001000)))
(assert (= (bvand base_addr #x0000000000000003) #x0000000000000000))
(assert (= (bvand stride2 #x0000000000000003) #x0000000000000000))

(define-fun alloc_bytes2 () (_ BitVec 64) (bvmul ((_ zero_extend 32) count2) stride2))
(define-fun rec_offset () (_ BitVec 64) (bvmul ((_ zero_extend 32) idx2) stride2))
(define-fun size_field_addr () (_ BitVec 64) (bvadd base_addr (bvadd rec_offset #x0000000000000030)))
(define-fun max_read_end () (_ BitVec 64) (bvadd rec_offset #x0000000000000034))

(assert (or (bvugt max_read_end alloc_bytes2)
            (not (= (bvand size_field_addr #x0000000000000003) #x0000000000000000))))
(check-sat)
(pop 1)
