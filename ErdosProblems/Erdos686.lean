/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

/-!
# Erdős Problem 686, conditional $k=3$, $N=4$ proof

This WIP module formalizes the elementary and finite parts of the Bennett-route
proof of the cleared integer variant
`(m+1)(m+2)(m+3) = 4(n+1)(n+2)(n+3)`, `m ≥ n+3`.

It is not yet listed in `proofs.yaml` or `Audit.lean`, because the final theorem
is not axiom-clean. Its current non-kernel footprint is:

* `approx_bound_for_cuberoot4`, the Bennett-derived bound `u ≤ 40846`;
* the generated axiom from `native_decide` in `cf_certificate_cuberoot4_dvd_aux`.
-/

namespace Erdos686

namespace Erdos686Variant

/--
External Bennett input: for coprime $u,v$ with
$u<v<2u$ and $0<4u^3-v^3\leq 60$, Bennett's irrationality estimate
for $\sqrt[3]{2}$ gives $u\leq 40846$.
-/
axiom approx_bound_for_cuberoot4
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hcop : Nat.Coprime u v)
    (huv : u < v) (hv2u : v < 2 * u)
    (hs : 0 < 4 * u ^ 3 - v ^ 3)
    (hs60 : 4 * u ^ 3 - v ^ 3 ≤ 60) :
    u ≤ 40846

set_option linter.style.nativeDecide false

/--
Native finite certificate replacing the continued-fraction table after the
divisibility step. For $26\leq u\leq40846$ and $s\mid60$, the number $4u^3-s$
is never a cube.

This is exact bounded arithmetic, but `native_decide` introduces a generated
native-decision axiom in `#print axioms`; do not advertise this file as a clean
hosted proof until this certificate is replaced by a kernel-checked proof.
-/
lemma cf_certificate_cuberoot4_dvd_aux :
    ∀ (u : Fin 40847) (s : Fin 61),
      26 ≤ (u : ℕ) →
      0 < (s : ℕ) →
      (s : ℕ) ∣ 60 →
      (Nat.nthRoot 3 (4 * (u : ℕ) ^ 3 - (s : ℕ))) ^ 3 =
        4 * (u : ℕ) ^ 3 - (s : ℕ) →
      False := by
  native_decide

set_option linter.style.nativeDecide true

/--
Continued-fraction-range exclusion, reduced here to a native finite
certificate using the already-proved divisibility condition $s\mid60$.
-/
lemma cf_certificate_cuberoot4
    (u v s : ℕ)
    (hu : 26 ≤ u) (huB : u ≤ 40846)
    (_hcop : Nat.Coprime u v)
    (_huv : u < v) (_hv2u : v < 2 * u)
    (happrox : 0 < 4 * u ^ 3 - v ^ 3 ∧ 4 * u ^ 3 - v ^ 3 ≤ 60)
    (hsdef : s = 4 * u ^ 3 - v ^ 3)
    (hsdvd : s ∣ 60) :
    False := by
  have hspos : 0 < s := by simpa [hsdef] using happrox.1
  have hsle60 : s ≤ 60 := Nat.le_of_dvd (by norm_num) hsdvd
  have hs_lt61 : s < 61 := by omega
  have hu_lt40847 : u < 40847 := by omega
  have hv3_eq : v ^ 3 = 4 * u ^ 3 - s := by
    rw [hsdef]
    omega
  have hcube :
      (Nat.nthRoot 3 (4 * u ^ 3 - s)) ^ 3 = 4 * u ^ 3 - s := by
    rw [← hv3_eq, Nat.nthRoot_pow (by norm_num : 3 ≠ 0) v]
  exact cf_certificate_cuberoot4_dvd_aux ⟨u, hu_lt40847⟩ ⟨s, hs_lt61⟩ hu hspos hsdvd hcube

lemma triple_product_eq_cube_sub (n : ℕ) :
    (n + 1) * (n + 2) * (n + 3) = (n + 2) ^ 3 - (n + 2) := by
  ring_nf
  omega

lemma curve_int_of_product (n m : ℕ)
    (heq : (m + 1) * (m + 2) * (m + 3) = 4 * ((n + 1) * (n + 2) * (n + 3))) :
    ((m + 2 : ℕ) : ℤ) ^ 3 - ((m + 2 : ℕ) : ℤ) =
      4 * (((n + 2 : ℕ) : ℤ) ^ 3 - ((n + 2 : ℕ) : ℤ)) := by
  have hnat : (m + 2) ^ 3 - (m + 2) = 4 * ((n + 2) ^ 3 - (n + 2)) := by
    rw [← triple_product_eq_cube_sub m, ← triple_product_eq_cube_sub n]
    exact heq
  have hmle : m + 2 ≤ (m + 2) ^ 3 := Nat.le_self_pow (by norm_num) (m + 2)
  have hnle : n + 2 ≤ (n + 2) ^ 3 := Nat.le_self_pow (by norm_num) (n + 2)
  exact_mod_cast hnat

lemma not_two_mul_le_of_curve (x y : ℕ) (hx : 0 < x)
    (hcurve : (y : ℤ) ^ 3 - (y : ℤ) = 4 * ((x : ℤ) ^ 3 - (x : ℤ))) :
    ¬ 2 * x ≤ y := by
  intro h2
  have h2z : (2 : ℤ) * x ≤ y := by exact_mod_cast h2
  let b : ℤ := 2 * (x : ℤ)
  let a : ℤ := (y : ℤ) - b
  let c : ℤ := (y : ℤ) ^ 2 + (y : ℤ) * b + b ^ 2 - 1
  have ha_nonneg : 0 ≤ a := by dsimp [a, b]; omega
  have hc_nonneg : 0 ≤ c := by
    dsimp [c, b]
    nlinarith [show (0 : ℤ) < x by exact_mod_cast hx, h2z]
  have hmono : b ^ 3 - b ≤ (y : ℤ) ^ 3 - (y : ℤ) := by
    have hfac : (y : ℤ) ^ 3 - (y : ℤ) - (b ^ 3 - b) = a * c := by
      dsimp [a, c]
      ring
    have hprod : 0 ≤ a * c := mul_nonneg ha_nonneg hc_nonneg
    nlinarith
  have hbase_gt : b ^ 3 - b > 4 * ((x : ℤ) ^ 3 - (x : ℤ)) := by
    dsimp [b]
    ring_nf
    have hxz : (0 : ℤ) < x := by exact_mod_cast hx
    have hx3 : (0 : ℤ) < (x : ℤ) ^ 3 := by positivity
    nlinarith
  nlinarith

lemma small_u_check_aux :
    ∀ (u : Fin 26) (v : Fin 52),
      0 < (u : ℕ) →
      (u : ℕ) < (v : ℕ) →
      (v : ℕ) < 2 * (u : ℕ) →
      0 < 4 * (u : ℕ) ^ 3 - (v : ℕ) ^ 3 →
      4 * (u : ℕ) ^ 3 - (v : ℕ) ^ 3 ≤ 60 →
      4 * (u : ℕ) ^ 3 - (v : ℕ) ^ 3 ∣ 60 →
      (u : ℕ) = 2 ∧ (v : ℕ) = 3 ∧ 4 * (u : ℕ) ^ 3 - (v : ℕ) ^ 3 = 5 := by
  decide

/--
The modular divisibility step in Lemma T. From
$D^2s=4u-v$, $s=4u^3-v^3$, and $\gcd(s,u)=1$, one gets $s\mid 60$.
-/
lemma s_dvd_sixty_of_coprime_s_u
    (u v D s : ℕ)
    (hDpos : 0 < D) (hspos : 0 < s)
    (hsu : Nat.Coprime s u)
    (hsdef : s = 4 * u ^ 3 - v ^ 3)
    (hD : D ^ 2 * s = 4 * u - v) :
    s ∣ 60 := by
  have hprod_pos : 0 < D ^ 2 * s := by positivity
  have hsub_pos : 0 < 4 * u - v := by simpa [hD] using hprod_pos
  have hv_le_4u : v ≤ 4 * u := by omega
  have hsdvd_sub : s ∣ 4 * u - v := by
    refine ⟨D ^ 2, ?_⟩
    rw [← hD, mul_comm]
  have hv_mod : v ≡ 4 * u [MOD s] := by
    rw [Nat.modEq_iff_dvd' hv_le_4u]
    exact hsdvd_sub
  have hspos_expr : 0 < 4 * u ^ 3 - v ^ 3 := by
    simpa [hsdef] using hspos
  have hv3_le : v ^ 3 ≤ 4 * u ^ 3 := by omega
  have hv3_mod : v ^ 3 ≡ 4 * u ^ 3 [MOD s] := by
    rw [Nat.modEq_iff_dvd' hv3_le]
    rw [← hsdef]
  have hcube_mod : (4 * u) ^ 3 ≡ 4 * u ^ 3 [MOD s] :=
    (hv_mod.pow 3).symm.trans hv3_mod
  have hle_cube : 4 * u ^ 3 ≤ (4 * u) ^ 3 := by
    nlinarith [show 0 ≤ u ^ 3 by omega]
  have hs_dvd_cube_diff : s ∣ (4 * u) ^ 3 - 4 * u ^ 3 := by
    rw [← Nat.modEq_iff_dvd' hle_cube]
    exact hcube_mod.symm
  have hdiff : (4 * u) ^ 3 - 4 * u ^ 3 = 60 * u ^ 3 := by
    ring_nf
    omega
  have hs_dvd_60u3 : s ∣ 60 * u ^ 3 := by
    rwa [hdiff] at hs_dvd_cube_diff
  exact (hsu.pow_right 3).dvd_of_dvd_mul_right hs_dvd_60u3

lemma coprime_s_u
    (u v s : ℕ)
    (hcop : Nat.Coprime u v)
    (hsdef : s = 4 * u ^ 3 - v ^ 3)
    (hspos : 0 < s) :
    Nat.Coprime s u := by
  refine Nat.coprime_of_dvd' ?_
  intro p hp hps hpu
  have hv3_le : v ^ 3 ≤ 4 * u ^ 3 := by
    by_contra hle
    rw [hsdef] at hspos
    omega
  have hs_add : s + v ^ 3 = 4 * u ^ 3 := by
    rw [hsdef]
    omega
  have hp_u3 : p ∣ u ^ 3 := by
    rw [show u ^ 3 = u * u ^ 2 by ring]
    exact dvd_mul_of_dvd_left hpu _
  have hp_4u3 : p ∣ 4 * u ^ 3 := dvd_mul_of_dvd_right hp_u3 4
  have hp_sum : p ∣ s + v ^ 3 := by rwa [hs_add]
  have hp_v3 : p ∣ v ^ 3 := (Nat.dvd_add_right hps).mp hp_sum
  have hp_v : p ∣ v := hp.dvd_of_dvd_pow hp_v3
  have hp_coprime_v : Nat.Coprime p v := hcop.coprime_dvd_left hpu
  exact hp_coprime_v.dvd_of_dvd_mul_right (by simpa using hp_v)

lemma scaled_nat_eq
    (D u v : ℕ) (hDpos : 0 < D) (hu : 0 < u) (hv2u : v < 2 * u)
    (hscaled_int : ((D : ℤ) ^ 2) * (4 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3) =
      4 * (u : ℤ) - (v : ℤ)) :
    let s := 4 * u ^ 3 - v ^ 3
    0 < s ∧ D ^ 2 * s = 4 * u - v := by
  intro s
  have hv_lt_4u : v < 4 * u := by nlinarith
  have hv_le_4u : v ≤ 4 * u := le_of_lt hv_lt_4u
  have hrhs_pos_int : (0 : ℤ) < 4 * (u : ℤ) - (v : ℤ) := by
    omega
  have hDsq_pos : (0 : ℤ) < (D : ℤ) ^ 2 := by positivity
  have hterm_pos_int : (0 : ℤ) < 4 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3 := by
    nlinarith
  have hv3_lt_int : (v : ℤ) ^ 3 < 4 * (u : ℤ) ^ 3 := by
    nlinarith
  have hv3_lt : v ^ 3 < 4 * u ^ 3 := by
    exact_mod_cast hv3_lt_int
  have hv3_le : v ^ 3 ≤ 4 * u ^ 3 := le_of_lt hv3_lt
  have hspos : 0 < s := by
    dsimp [s]
    omega
  refine ⟨hspos, ?_⟩
  apply Nat.cast_injective (R := ℤ)
  dsimp [s]
  rw [Nat.cast_sub hv3_le, Nat.cast_sub hv_le_4u]
  simpa [Nat.cast_pow] using hscaled_int

/--
The finite check below the continued-fraction range. If $1\leq u<26$,
$u<v<2u$, $0<4u^3-v^3\leq 60$, and $4u^3-v^3$ divides $60$, then
the only possible pair is $(u,v)=(2,3)$ and the defect is $5$.
-/
lemma small_u_check
    (u v s : ℕ)
    (hu : 0 < u) (hu26 : u < 26)
    (huv : u < v) (hv2u : v < 2 * u)
    (hspos : 0 < 4 * u ^ 3 - v ^ 3)
    (hs60 : 4 * u ^ 3 - v ^ 3 ≤ 60)
    (hsdef : s = 4 * u ^ 3 - v ^ 3)
    (hsdvd : s ∣ 60) :
    u = 2 ∧ v = 3 ∧ s = 5 := by
  subst s
  have hv52 : v < 52 := by nlinarith
  exact small_u_check_aux ⟨u, hu26⟩ ⟨v, hv52⟩ hu huv hv2u hspos hs60 hsdvd

/--
Conditional Lemma T. The only non-elementary inputs are the two external
certificates above; the low range is checked exactly in `small_u_check`.
-/
theorem lemmaT_conditional
    (u v D s : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hDpos : 0 < D) (hspos : 0 < s)
    (hcop : Nat.Coprime u v)
    (huv : u < v) (hv2u : v < 2 * u)
    (hsdef : s = 4 * u ^ 3 - v ^ 3)
    (hD : D ^ 2 * s = 4 * u - v)
    (hs60 : s ∣ 60) :
    (u, v, D, s) = (2, 3, 1, 5) := by
  have hspos_expr : 0 < 4 * u ^ 3 - v ^ 3 := by
    simpa [hsdef] using hspos
  have hsle60_expr : 4 * u ^ 3 - v ^ 3 ≤ 60 := by
    rw [← hsdef]
    exact Nat.le_of_dvd (by norm_num) hs60
  have huB : u ≤ 40846 :=
    approx_bound_for_cuberoot4 u v hu hv hcop huv hv2u hspos_expr hsle60_expr
  by_cases hu26 : 26 ≤ u
  · exact (cf_certificate_cuberoot4 u v s hu26 huB hcop huv hv2u
      ⟨hspos_expr, hsle60_expr⟩ hsdef hs60).elim
  · have hu_lt26 : u < 26 := by omega
    obtain ⟨hu2, hv3, hs5⟩ :=
      small_u_check u v s hu hu_lt26 huv hv2u hspos_expr hsle60_expr hsdef hs60
    subst u
    subst v
    subst s
    norm_num at hD
    have hDsq : D ^ 2 = 1 := by nlinarith
    have hDle : D ≤ 1 := by nlinarith
    have hD1 : D = 1 := by omega
    subst D
    rfl

/--
Arithmetic reduction from a solution of the cleared $k=3$, $N=4$
equation to the primitive Lemma T data. This carries out the substitution
$x=n+2$, $y=m+2$, normalizes by $D=\gcd(x,y)$, and proves the primitive
conditions needed by Lemma T.
-/
theorem primitive_reduction_to_LemmaT
    (n m : ℕ)
    (hm : m ≥ n + 3)
    (heq : (m + 1) * (m + 2) * (m + 3) = 4 * ((n + 1) * (n + 2) * (n + 3))) :
    ∃ u v D s : ℕ,
      0 < u ∧ 0 < v ∧ 0 < D ∧ 0 < s ∧
      Nat.Coprime u v ∧
      u < v ∧ v < 2 * u ∧
      s = 4 * u ^ 3 - v ^ 3 ∧
      D ^ 2 * s = 4 * u - v ∧
      Nat.Coprime s u ∧
      D * u = n + 2 ∧
      D * v = m + 2 := by
  let x := n + 2
  let y := m + 2
  have hx : 0 < x := by dsimp [x]; omega
  have hy : 0 < y := by dsimp [y]; omega
  have hxy3 : x + 3 ≤ y := by dsimp [x, y]; omega
  have hxy : x < y := by omega
  have hcurve : (y : ℤ) ^ 3 - (y : ℤ) = 4 * ((x : ℤ) ^ 3 - (x : ℤ)) := by
    dsimp [x, y]
    exact curve_int_of_product n m heq
  have hy_lt_2x : y < 2 * x := by
    exact lt_of_not_ge (not_two_mul_le_of_curve x y hx hcurve)
  let D := Nat.gcd x y
  let u := x / D
  let v := y / D
  have hDpos : 0 < D := by
    dsimp [D]
    exact Nat.gcd_pos_of_pos_left y hx
  have hDvdx : D ∣ x := by
    dsimp [D]
    exact Nat.gcd_dvd_left x y
  have hDvdy : D ∣ y := by
    dsimp [D]
    exact Nat.gcd_dvd_right x y
  have hx_eq : D * u = x := by
    dsimp [u]
    exact Nat.mul_div_cancel' hDvdx
  have hy_eq : D * v = y := by
    dsimp [v]
    exact Nat.mul_div_cancel' hDvdy
  have hD_le_x : D ≤ x := Nat.le_of_dvd hx hDvdx
  have hD_le_y : D ≤ y := Nat.le_of_dvd hy hDvdy
  have hu : 0 < u := by
    dsimp [u]
    exact Nat.div_pos hD_le_x hDpos
  have hv : 0 < v := by
    dsimp [v]
    exact Nat.div_pos hD_le_y hDpos
  have hcop : Nat.Coprime u v := by
    dsimp [u, v, D]
    exact Nat.coprime_div_gcd_div_gcd hDpos
  have huv : u < v := by nlinarith
  have hv2u : v < 2 * u := by nlinarith
  have hxz : (x : ℤ) = (D : ℤ) * (u : ℤ) := by exact_mod_cast hx_eq.symm
  have hyz : (y : ℤ) = (D : ℤ) * (v : ℤ) := by exact_mod_cast hy_eq.symm
  have hscaled_int : ((D : ℤ) ^ 2) * (4 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3) =
      4 * (u : ℤ) - (v : ℤ) := by
    have hcurve' := hcurve
    rw [hxz, hyz] at hcurve'
    have hDnz : (D : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hDpos
    have hmul : (D : ℤ) *
        (((D : ℤ) ^ 2) * (4 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3) -
          (4 * (u : ℤ) - (v : ℤ))) = 0 := by
      ring_nf at hcurve' ⊢
      nlinarith
    have hzero : ((D : ℤ) ^ 2) * (4 * (u : ℤ) ^ 3 - (v : ℤ) ^ 3) -
        (4 * (u : ℤ) - (v : ℤ)) = 0 := by
      exact (mul_eq_zero.mp hmul).resolve_left hDnz
    exact sub_eq_zero.mp hzero
  let s := 4 * u ^ 3 - v ^ 3
  obtain ⟨hspos, hD⟩ := scaled_nat_eq D u v hDpos hu hv2u hscaled_int
  have hsdef : s = 4 * u ^ 3 - v ^ 3 := rfl
  have hsu : Nat.Coprime s u := coprime_s_u u v s hcop hsdef hspos
  refine ⟨u, v, D, s, hu, hv, hDpos, hspos, hcop, huv, hv2u, hsdef, hD, hsu, ?_, ?_⟩
  · dsimp [D, u, x] at hx_eq ⊢
    exact hx_eq
  · dsimp [D, v, y] at hy_eq ⊢
    exact hy_eq

/--
Cleared integer form of the $k=3$, $N=4$ variant:
there are no natural numbers $n,m$ with $m\geq n+3$ and
$(m+1)(m+2)(m+3)=4(n+1)(n+2)(n+3)$.
-/
theorem no_solution_cleared :
    ¬ ∃ n m : ℕ,
      m ≥ n + 3 ∧
      (m + 1) * (m + 2) * (m + 3) = 4 * ((n + 1) * (n + 2) * (n + 3)) := by
  rintro ⟨n, m, hm, heq⟩
  obtain ⟨u, v, D, s, hu, hv, hDpos, hspos, hcop, huv, hv2u, hsdef, hD, hsu,
    hDu, hDv⟩ := primitive_reduction_to_LemmaT n m hm heq
  have hs60 := s_dvd_sixty_of_coprime_s_u u v D s hDpos hspos hsu hsdef hD
  have htuple := lemmaT_conditional u v D s hu hv hDpos hspos hcop huv hv2u hsdef hD hs60
  have htuple_components : u = 2 ∧ v = 3 ∧ D = 1 ∧ s = 5 := by
    simpa using htuple
  obtain ⟨hu2, hv3, hD1, hs5⟩ := htuple_components
  subst u
  subst v
  subst D
  subst s
  norm_num at hDu hDv
  omega

end Erdos686Variant

end Erdos686
