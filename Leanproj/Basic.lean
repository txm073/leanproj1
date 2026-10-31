import Mathlib

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

theorem perm_prod_eq
  (l1 l2 : List Nat)
  (h : List.Perm l1 l2)
    : (l1.prod = l2.prod) := by
  sorry

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
    have h_all :=
      append_to_factorisation (n1 * ls.prod) l l_prime (l1 ++ ls) h_comb
    have h_prod : ls.prod * l = n2 := by
      rw [←ht_prod, mul_comm, List.prod_cons]
    -- have h_perm_factorisation : IsPrimeFactorisation n (l1::l2++l3) → IsPrimeFactorisation
    rw [←List.cons_append, mul_assoc, h_prod] at h_all
    rcases h_all with ⟨hf1, hf2⟩
    -- Prove the reordered list has the same product
    rw [List.cons_append, List.prod_cons, mul_comm l, List.prod_append] at hf2
    rw [mul_assoc, mul_comm (ls.prod) l, ←List.prod_cons, ←List.prod_append] at hf2
    -- Prove the reordered list still contains only primes
    have hf3 : ∀ p ∈ l1++l::ls, Nat.Prime p := by sorry
    -- Combine these
    exact And.intro hf3 hf2
