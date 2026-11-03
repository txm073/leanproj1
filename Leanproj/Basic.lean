import Mathlib

/-!
Helper lemmas and a theorem to prove existence of a prime factorisation
for any natural number n ≥ 2, using only basic tactics and Mathlib lemmas
involving basic arithmetic and list operations
-/

/-- A prime factorisation of a natural number n is defined as
a list of natural numbers that are primes and a product equal to n -/
structure IsPrimeFactorisation (n : ℕ) (L : List ℕ) where
  all_primes : ∀ p ∈ L, Nat.Prime p
  prod_eq : L.prod = n

/-- A prime number p has factorisation [p] -/
lemma prime_has_factorisation (p : ℕ) (hp : Nat.Prime p) :
    IsPrimeFactorisation p [p] := by
  constructor
  · intro q hq
    rw [List.mem_singleton] at hq
    rwa [hq]
  · simp

/-- If a factorisation is an empty list then n = 1 -/
lemma empty_factorisation_is_one (l : List Nat) (hp : l.isEmpty) (n : ℕ)
    (hl : IsPrimeFactorisation n l) : n = 1 := by
  rw [List.isEmpty_iff] at hp
  simpa [hp, eq_comm] using hl.prod_eq

/-- The converse, if n = 1 then the empty list is a factorisation for n -/
lemma one_has_empty_factorisation (n : ℕ) (hn : n = 1) : IsPrimeFactorisation n [] := by
  exact ⟨by simp, by simp [hn]⟩

/-- Any permutation of a factorisation for n is also a valid factorisation for n -/
lemma perm_is_factorisation (n : ℕ) (l1 l2 : List Nat)
    (hf : IsPrimeFactorisation n l1) (hp : List.Perm l1 l2) : IsPrimeFactorisation n l2 := by
  constructor
  · intro p h_perm
    rw [←hp.mem_iff] at h_perm
    exact hf.all_primes p h_perm
  · rcases hf with ⟨_, h_prod⟩
    rw [←h_prod, hp.prod_eq]

/-- If n has factorisation [p₁,...,pₖ], and p is a prime number,
n * p has factorisation [p₁,...,pₖ,p] -/
lemma append_to_factorisation (n p : ℕ) (hp : Nat.Prime p) (l : List ℕ)
    (h : IsPrimeFactorisation n l) : IsPrimeFactorisation (n * p) (List.cons p l) := by
  constructor
  · simp only [List.mem_cons, forall_eq_or_imp]
    exact And.intro hp h.all_primes
  · simp [List.prod_cons, Nat.mul_comm, h.prod_eq]

/-- Two factorisations for n₁ and n₂ can be concatenated to obtain a factorisation for n₁n₂ -/
lemma combine_factorisations (n1 n2 : ℕ) (l1 l2 : List Nat) (h1 : IsPrimeFactorisation n1 l1)
    (h2 : IsPrimeFactorisation n2 l2) : IsPrimeFactorisation (n1 * n2) (l1 ++ l2) := by
  induction l2 generalizing n2 with
  | nil =>
    simp only [List.append_nil]
    have n2_eq_one : n2 = 1 :=
      empty_factorisation_is_one [] (by simp only [List.isEmpty_nil]) n2 h2
    simpa [n2_eq_one, Nat.mul_one]
  | cons l ls ih =>
    have l_prime : Nat.Prime l := by exact h2.all_primes l (by simp only [List.mem_cons, true_or])
    have h_tail : IsPrimeFactorisation ls.prod ls := by
      constructor
      · intro p hp
        exact h2.all_primes p (by simp [hp])
      · rfl
    have h_comb : IsPrimeFactorisation (n1 * ls.prod) (l1 ++ ls) := ih ls.prod h_tail
    have h_all := append_to_factorisation (n1 * ls.prod) l l_prime (l1 ++ ls) h_comb
    have h_prod : ls.prod * l = n2 := by rw [←h2.prod_eq, mul_comm, List.prod_cons]
    have h_perm : List.Perm (l::l1++ls) (l1++l::ls) := by
      change List.Perm (([l] ++ l1) ++ ls) (l1 ++ ([l] ++ ls))
      have perm_assoc := List.perm_append_comm_assoc [l] l1 ls
      rw [←List.append_assoc]
      repeat rw [←List.append_assoc] at perm_assoc
      exact perm_assoc
    rw [←List.cons_append, mul_assoc, h_prod] at h_all
    exact perm_is_factorisation (n1 * n2) (l::l1++ls) (l1++l::ls) h_all h_perm

/-- If n is not prime, ∃ a, b ∈ ℕ with n = ab, 1 < a, b < n -/
lemma factors_exist (n : ℕ) (hn : n ≥ 2) (h : ¬Nat.Prime n) :
    ∃ a b : ℕ, n = a * b ∧ 1 < a ∧ a < n ∧ 1 < b ∧ b < n := by
  rw [Nat.prime_def] at h
  push Not at h
  specialize h hn
  obtain ⟨a, ⟨b, h_prod⟩, a_ne_one, a_ne_n⟩ := h
  refine ⟨a, b, h_prod, ?_⟩
  by_cases ha : a = 0
  · grind
  · by_cases hb : b = 0
    · grind
    · by_cases hb' : b = 1
      · grind
      · have zero_lt_a : 0 < a := by grind
        have zero_lt_b : 0 < b := by grind
        have one_lt_a : 1 < a := by grind
        have one_lt_b : 1 < b := by grind
        refine ⟨by grind, ?_, by grind, ?_⟩
        · nth_rw 1 [h_prod, ←mul_one a]
          exact mul_lt_mul_of_pos_left one_lt_b zero_lt_a
        · nth_rw 1 [h_prod, ←one_mul b]
          exact mul_lt_mul_of_pos_right one_lt_a zero_lt_b

-- Main result: Every natural number n ≥ 2 has a prime factorisation
theorem factorisation_exists (n : ℕ) (hn : n >= 2) :
    (∃ l : List Nat, IsPrimeFactorisation n l) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_prime : Nat.Prime n
    · use [n]
      exact prime_has_factorisation n h_prime
    · obtain ⟨a, b, prod_eq, a_gt_one, a_lt_n, b_gt_one, b_lt_n⟩ := factors_exist n hn h_prime
      obtain ⟨la, ha⟩ := ih a a_lt_n a_gt_one
      obtain ⟨lb, hb⟩ := ih b b_lt_n b_gt_one
      have hab := combine_factorisations a b la lb ha hb
      rw [←prod_eq] at hab
      use la++lb

/-- Bezout's lemma: the gcd of a and b can be written as an integer linear combination -/
lemma gcd_int_linear_comb (a b : ℕ) : ∃ (x y : ℤ), a * x + b * y = Nat.gcd a b := by
  -- Simple wrapper around Mathlib's built in result, I did not prove this from scratch
  -- due to time and code size constraints
  use Nat.gcdA a b, Nat.gcdB a b
  rw [←Nat.gcd_eq_gcd_ab]

/-- If n | ab and a and n are coprime, n | b -/
lemma coprime_dvd_prod (n a b : ℕ) (h : n ∣ a * b) (hc : Nat.Coprime a n) : n ∣ b := by
  unfold Nat.Coprime at hc
  obtain ⟨x, y, h'⟩ := gcd_int_linear_comb a n
  rw [hc] at h'
  have h_mul : b * (a * x + n * y) = b * 1 := by grind
  have h_dvd : ↑n ∣ b * (a * x + n * y) := by
    rw [Int.mul_add]
    apply Int.dvd_add
    · rw [Int.mul_comm a x, Int.mul_comm, Int.mul_assoc]
      apply Int.dvd_mul_of_dvd_right
      exact_mod_cast h
    · rw [Int.mul_comm, Int.mul_assoc, Int.mul_comm]
      apply Int.dvd_mul_of_dvd_right
      exact_mod_cast (Int.dvd_refl n)
  have h_dvd' : ↑n ∣ ↑b * 1 := by
    rw [h_mul] at h_dvd
    exact_mod_cast h_dvd
  rwa [mul_one] at h_dvd'

/-- If p is prime and p | ab, p | a or p | b -/
lemma prime_dvd_prod (p a b : ℕ) (hp : Nat.Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases ha : p ∣ a
  · exact Or.inl ha
  · have hc : Nat.Coprime a p := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd.mpr ha
    exact Or.inr (coprime_dvd_prod p a b h hc)

/-- If p is prime and divides n, it must divide one of it's prime factors -/
lemma prime_dvd_prod_dvd_factor (p n : ℕ) (l : List ℕ) (hf : IsPrimeFactorisation n l)
    (hp : Nat.Prime p) (h : p ∣ n) : ∃ q ∈ l, p ∣ q := by
  induction l generalizing n with
  | nil =>
    have hn : n = 1 := empty_factorisation_is_one [] (by simp) n hf
    have hp' : ¬p ∣ n := by
      rw [hn]
      exact hp.not_dvd_one
    contradiction
  | cons q qs ih =>
    have q_prime : Nat.Prime q := hf.all_primes q (by simp)
    have h_tail : IsPrimeFactorisation qs.prod qs := by
      constructor
      · intro r hr
        exact hf.all_primes r (by simp [hr])
      · rfl
    by_cases h_div_prod : p ∣ qs.prod
    · obtain ⟨q', hq, hpq⟩ := ih qs.prod h_tail h_div_prod
      use q'
      exact And.intro (List.mem_cons_of_mem q hq) hpq
    · have hq_or_tail : p ∣ q ∨ p ∣ qs.prod := by
        have h_prod := hf.prod_eq
        rw [List.prod_cons] at h_prod
        rw [←h_prod] at h
        exact prime_dvd_prod p q (qs.prod) hp h
      have hpq : p ∣ q := by
        rcases hq_or_tail with hq | htail
        · exact hq
        · contradiction
      use q
      exact And.intro (by simp) hpq

lemma factorisation_subset (p n : ℕ) (hp : Nat.Prime p) (l1 l2 : List ℕ)
    (h1 : IsPrimeFactorisation n l1) (h2 : IsPrimeFactorisation n l2) (h : p ∈ l1) : p ∈ l2 := by
  have h_div : p ∣ n := by
    rw [←h1.prod_eq]
    exact List.dvd_prod h
  obtain ⟨q, hq_mem, hpq⟩ := prime_dvd_prod_dvd_factor p n l2 h2 hp h_div
  have hq : Nat.Prime q := h2.all_primes q hq_mem
  have h_eq : q = p := (hq.dvd_iff_eq hp.ne_one).mp hpq
  rw [←h_eq]
  exact hq_mem

lemma factorisation_remove_prime (n p : ℕ) (l : List ℕ)
  (hf : IsPrimeFactorisation n l) (hp : Nat.Prime p) (hmem : p ∈ l) :
    ∃ before after : List ℕ,
    l = before ++ [p] ++ after ∧
    IsPrimeFactorisation (n / p) (before ++ after) := by
  induction l generalizing n with
  | nil => simp at hmem
  | cons q qs ih =>
    have h_q_prime : Nat.Prime q := by simp [hf.all_primes]
    have h_prod : n / q = qs.prod := by
      rw [←hf.prod_eq, List.prod_cons]
      exact Nat.mul_div_right qs.prod (Nat.pos_of_ne_zero h_q_prime.ne_zero)
    have hqs : IsPrimeFactorisation qs.prod qs := by
      constructor
      · intro r hr
        exact hf.all_primes r (by simp [hr])
      · rfl
    by_cases hq : p = q
    · use [], qs
      rw [List.nil_append qs, List.nil_append [p], hq, List.singleton_append]
      constructor
      · rfl
      · rwa [h_prod]
    · have hmem' : p ∈ qs := by
        rw [List.mem_cons] at hmem
        exact hmem.resolve_left hq
      obtain ⟨before, after, hsplit, hf'⟩ := ih qs.prod hqs hmem'
      refine ⟨q :: before, after, ?_, ?_⟩
      · simp [hsplit]
      · have hnew := append_to_factorisation (qs.prod / p) q h_q_prime (before ++ after) hf'
        have hnum : (qs.prod / p) * q = n / p := by
          have hp' : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
          have hq_div : q ∣ n := by
            rw [←hf.prod_eq]
            exact List.dvd_prod (by simp)
          rw [Nat.div_mul_right_comm (List.dvd_prod hmem'), ←h_prod, Nat.div_mul_cancel hq_div]
        rwa [←hnum]

theorem factorisation_unique (n : ℕ) (l1 l2 : List ℕ)
    (h1 : IsPrimeFactorisation n l1) (h2 : IsPrimeFactorisation n l2) : List.Perm l1 l2 := by
  induction l1 generalizing n l2 with
  | nil =>
    have n_eq_one : n = 1 := empty_factorisation_is_one [] (by simp [List.isEmpty_nil]) n h1
    have l2_empty : l2.isEmpty := by
      have hprod : l2.prod = 1 := by
        rw [h2.prod_eq, n_eq_one]
      cases l2 with
      | nil => simp
      | cons q qs =>
        simp [List.prod_cons] at hprod
        have hq : 1 < q := (h2.all_primes q (by simp)).one_lt
        grind
    rw [List.perm_comm, List.perm_nil]
    apply List.isEmpty_iff.mp l2_empty
  | cons p ps ih =>
    have hp : Nat.Prime p := h1.all_primes p (by simp)
    have hp_mem : p ∈ l2 := factorisation_subset p n hp (p :: ps) l2 h1 h2 (by simp)
    obtain ⟨before, after, hsplit, h2'⟩ := factorisation_remove_prime n p l2 h2 hp hp_mem
    have h1' : IsPrimeFactorisation (n / p) ps := by
      constructor
      · intro r hr
        exact h1.all_primes r (by simp [hr])
      · rw [←h1.prod_eq, List.prod_cons, eq_comm]
        have hp' : 0 < p := Nat.pos_of_ne_zero hp.ne_zero
        exact Nat.mul_div_cancel_left ps.prod hp'
    obtain h_perm := ih (n / p) (before ++ after) h1' h2'
    have h_perm' : List.Perm (p::before ++ after) (before ++ [p] ++ after) := by
      rw [←List.singleton_append, List.perm_append_right_iff]
      exact List.perm_append_comm
    rw [←hsplit] at h_perm'
    rw [←List.perm_cons p] at h_perm
    exact List.Perm.trans h_perm h_perm'
