import Mathlib
import Mathlib.Data.List.Permutation

def IsPrimeFactorisation (n : Nat) (L : List Nat) : Prop :=
  (∀ p ∈ L, Nat.Prime p) ∧ L.prod = n

theorem prime_has_factorisation (p : Nat) (hp : Nat.Prime p)
  : IsPrimeFactorisation p [p] := by
  constructor
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rw [hq]
    exact hp
  · simp only [List.prod_cons, List.prod_nil, mul_one]

theorem one_has_factorisation : IsPrimeFactorisation 1 [] := by
  constructor
  · intro p hp
    simp only [List.not_mem_nil] at hp
  · simp only [List.prod_nil]

theorem empty_factorisation_is_one
  (l : List Nat)
  (hp : l.isEmpty)
  (n : Nat)
  (hl : IsPrimeFactorisation n l)
    : n = 1 := by
  rcases hl with ⟨_, h⟩
  rw [List.isEmpty_iff] at hp
  rw [hp, List.prod_nil] at h
  exact h.symm

theorem append_to_factorisation
  (n p : Nat)
  (hp : Nat.Prime p)
  (l : List Nat)
  (h : IsPrimeFactorisation n l)
    : IsPrimeFactorisation (n * p) (List.cons p l) := by
  constructor
  · rcases h with ⟨h', _⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact And.intro hp h'
  · simp only [List.prod_cons]
    rcases h with ⟨_, hn⟩
    rw [Nat.mul_comm, hn]

theorem perm_is_factorisation
  (n : Nat)
  (l1 l2 : List Nat)
  (hf : IsPrimeFactorisation n l1)
  (hp : List.Perm l1 l2)
    : IsPrimeFactorisation n l2 := by
  constructor
  -- All elements of l2 are primes
  · intro p h_perm
    rw [←hp.mem_iff] at h_perm
    rcases hf with ⟨h_is_prime, _⟩
    specialize h_is_prime p
    specialize h_is_prime h_perm
    exact h_is_prime
  -- l1.prod = l2.prod = n
  · rcases hf with ⟨_, h_prod⟩
    rw [←h_prod, hp.prod_eq]

theorem combine_factorisations
  (n1 n2 : Nat)
  (l1 l2 : List Nat)
  (h1 : IsPrimeFactorisation n1 l1)
  (h2 : IsPrimeFactorisation n2 l2)
    : IsPrimeFactorisation (n1 * n2) (l1 ++ l2) := by
  induction l2 generalizing n2 with
  | nil =>
    simp only [List.append_nil]
    have n2_eq_one : n2 = 1 :=
      empty_factorisation_is_one [] (by simp only [List.isEmpty_nil]) n2 h2
    simp only [n2_eq_one, Nat.mul_one]
    exact h1
  | cons l ls ih =>
    rcases h2 with ⟨ht_primes, ht_prod⟩
    have l_prime : Nat.Prime l := by
      exact ht_primes l (by simp only [List.mem_cons, true_or])
    -- Tail is a valid factorisation
    have h_tail : IsPrimeFactorisation ls.prod ls := by
      constructor
      · intro p hp
        exact ht_primes p (by simp [hp])
      · rfl
    -- Combining the first list and the tail is a valid factorisation
    have h_comb : IsPrimeFactorisation (n1 * ls.prod) (l1 ++ ls) :=
      ih ls.prod h_tail
    -- Combining the new list with the head element
    have h_all :=
      append_to_factorisation (n1 * ls.prod) l l_prime (l1 ++ ls) h_comb
    have h_prod : ls.prod * l = n2 := by
      rw [←ht_prod, mul_comm, List.prod_cons]
    rw [←List.cons_append, mul_assoc, h_prod] at h_all
    -- Show the new constructed list is a permutation of l1::l2
    have h_perm : List.Perm (l::l1++ls) (l1++l::ls) := by
      change List.Perm (([l] ++ l1) ++ ls) (l1 ++ ([l] ++ ls))
      rw [←List.append_assoc]
      have perm_assoc := List.perm_append_comm_assoc [l] l1 ls
      repeat rw [←List.append_assoc] at perm_assoc
      exact perm_assoc
    exact perm_is_factorisation (n1 * n2) (l::l1++ls) (l1++l::ls) h_all h_perm

theorem factors_exist (n : Nat) (h : ¬Nat.Prime n)
  : ∃ a b : Nat, n = a * b
    ∧ 1 < a ∧ a < n
    ∧ 1 < b ∧ b < n := by
  -- h_prime : p < 2 ∨ ∃ m ∈ ℕ, m | p ∧ m ≠ 1 ∧ m ≠ p
  by_contra h_prime
  apply h
  push_neg at h_prime



-- Main result
theorem factorisation_exists
  (n : Nat)
  (hn : n >= 2)
    : (∃ l : List Nat, IsPrimeFactorisation n l) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h_base : n = 2
    · use [2]
      rw [h_base]
      exact prime_has_factorisation 2 Nat.prime_two
    · by_cases h_prime : Nat.Prime n
      · use [n]
        exact prime_has_factorisation n h_prime
      · obtain ⟨a, b, prod_eq, a_gt_one, a_lt_n, b_gt_one, b_lt_n⟩ := factors_exist n h_prime
        have a_factorisation : ∃ la : List Nat, IsPrimeFactorisation a la := by
          specialize ih a a_lt_n a_gt_one
          exact ih
        have b_factorisation : ∃ lb : List Nat, IsPrimeFactorisation b lb := by
          specialize ih b b_lt_n b_gt_one
          exact ih
        obtain ⟨la, ha⟩ := a_factorisation
        obtain ⟨lb, hb⟩ := b_factorisation
        have hab := combine_factorisations a b la lb ha hb
        rw [←prod_eq] at hab
        use la++lb
