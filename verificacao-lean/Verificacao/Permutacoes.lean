module

public import Mathlib

/-!
# |S_n| = n!, seguindo a demonstração do autor (`permutacoes/main.tex`)

`A_n` é representado por `Fin n` e `S_n` por `Equiv.Perm (Fin n)`.
O elemento `a_{n+1}` de `A_{n+1}` é `Fin.last n`.
-/

open Equiv Finset

/-- `S_m^{j,i}`: as permutações de `Fin m` que levam `j` em `i`. -/
public def fibra (m : ℕ) (j i : Fin m) : Finset (Perm (Fin m)) :=
  univ.filter (fun σ => σ j = i)

/-- `⋃_i S_m^{j,i} = S_m`. -/
public theorem uniao_fibras (m : ℕ) (j : Fin m) : univ.biUnion (fibra m j) = univ := by
  ext σ
  simp [fibra]

/-- Para `j` fixo, os `S_m^{j,i}` são disjuntos dois a dois. -/
public theorem fibras_disjuntas (m : ℕ) (j : Fin m) {i i' : Fin m} (h : i ≠ i') :
    Disjoint (fibra m j i) (fibra m j i') := by
  rw [Finset.disjoint_left]
  intro σ h1 h2
  simp only [fibra, mem_filter] at h1 h2
  exact h (h1.2.symm.trans h2.2)

/-- `|S_m| = ∑_i |S_m^{j,i}|` (união disjunta). -/
public theorem card_eq_sum_fibras (m : ℕ) (j : Fin m) :
    (univ : Finset (Perm (Fin m))).card = ∑ i, (fibra m j i).card := by
  unfold fibra
  exact card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin m) => σ j) (by simp)

/-- "Por simetria": `|S_m^{j,i}| = |S_m^{j',i'}|`, via `σ ↦ (i i') ∘ σ ∘ (j j')`. -/
public theorem card_fibra_simetria (m : ℕ) (j i j' i' : Fin m) :
    (fibra m j i).card = (fibra m j' i').card := by
  refine Finset.card_nbij' (fun σ => swap i i' * σ * swap j j')
    (fun τ => swap i i' * τ * swap j j') ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [fibra, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [Perm.mul_apply, hσ]
  · intro τ hτ
    simp only [fibra, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
    simp [Perm.mul_apply, hτ]
  · intro σ _
    simp [mul_assoc]
  · intro τ _
    simp [mul_assoc]

/-- `λ_{n,n+1}`: pares `(σ^{(n)}, σ^{(n+1)})` em que `σ^{(n+1)}` estende `σ^{(n)}`. -/
public def lam (n : ℕ) : Finset (Perm (Fin n) × Perm (Fin (n + 1))) :=
  univ.filter (fun x => ∀ k : Fin n, x.2 k.castSucc = (x.1 k).castSucc)

/-- `x ∈ λ_{n,n+1} ⇒ σ^{(n+1)}(a_{n+1}) = a_{n+1}`. -/
public theorem lam_fixa_ultimo {n : ℕ} {x : Perm (Fin n) × Perm (Fin (n + 1))}
    (hx : x ∈ lam n) : x.2 (Fin.last n) = Fin.last n := by
  simp only [lam, mem_filter, mem_univ, true_and] at hx
  by_contra h
  obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr h
  have h2 : x.2 (Fin.last n) = x.2 (x.1.symm k).castSucc := by
    rw [hx, Equiv.apply_symm_apply, hk]
  exact Fin.castSucc_ne_last _ (x.2.injective h2).symm

/-- A extensão de `τ` a `Fin (n+1)` que fixa o último elemento. -/
public def estende {n : ℕ} (τ : Perm (Fin n)) : Perm (Fin (n + 1)) where
  toFun := Fin.lastCases (Fin.last n) (fun k => (τ k).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun k => (τ.symm k).castSucc)
  left_inv x := by cases x using Fin.lastCases <;> simp
  right_inv x := by cases x using Fin.lastCases <;> simp

/-- A restrição a `Fin n` de uma permutação de `Fin (n+1)` que fixa o último elemento. -/
public def restringe {n : ℕ} (σ : Perm (Fin (n + 1))) (h : σ (Fin.last n) = Fin.last n) :
    Perm (Fin n) where
  toFun k := (σ k.castSucc).castPred (by
    intro e
    exact Fin.castSucc_ne_last k (σ.injective (e.trans h.symm)))
  invFun k := (σ.symm k.castSucc).castPred (by
    intro e
    have h' : σ.symm (Fin.last n) = Fin.last n := by rw [Equiv.symm_apply_eq]; exact h.symm
    exact Fin.castSucc_ne_last k (σ.symm.injective (e.trans h'.symm)))
  left_inv k := by simp
  right_inv k := by simp

/-- Existência e unicidade da extensão: `(τ, σ) ∈ λ ↔ σ = estende τ`. -/
public theorem mem_lam_iff {n : ℕ} (τ : Perm (Fin n)) (σ : Perm (Fin (n + 1))) :
    (τ, σ) ∈ lam n ↔ σ = estende τ := by
  constructor
  · intro hx
    have hl := lam_fixa_ultimo hx
    simp only [lam, mem_filter, mem_univ, true_and] at hx
    ext x
    cases x using Fin.lastCases with
    | last => simp [estende, hl]
    | cast k => simp [estende, hx k]
  · rintro rfl
    simp [lam, estende]

/-- `|λ_{n,n+1}| = |S_n|` (primeira projeção, pela extensão única). -/
public theorem card_lam_eq_card_perm (n : ℕ) :
    (lam n).card = (univ : Finset (Perm (Fin n))).card := by
  refine Finset.card_nbij' Prod.fst (fun τ => (τ, estende τ)) ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro τ _; simp [(mem_lam_iff τ _).mpr rfl]
  · intro x hx
    have hx' : (x.1, x.2) ∈ lam n := hx
    rw [mem_lam_iff] at hx'
    ext <;> simp [hx']
  · intro τ _; rfl

/-- `|λ_{n,n+1}| = |S_{n+1}^{n+1,n+1}|` (segunda projeção). -/
public theorem card_lam_eq_card_fibra (n : ℕ) :
    (lam n).card = (fibra (n + 1) (Fin.last n) (Fin.last n)).card := by
  refine Finset.card_bij' (fun x _ => x.2)
    (fun σ hσ => (restringe σ (by simpa [fibra] using hσ), σ)) ?_ ?_ ?_ ?_
  · intro x hx; simpa [fibra] using lam_fixa_ultimo hx
  · intro σ hσ
    simp [lam, restringe]
  · intro x hx
    have hx' := hx
    simp only [lam, mem_filter, mem_univ, true_and] at hx'
    ext k
    · simp [restringe, hx' k]
    · rfl
  · intro σ _; rfl

/-- `|S_{n+1}| = (n+1)·|S_n|`. -/
public theorem card_succ (n : ℕ) :
    (univ : Finset (Perm (Fin (n + 1)))).card = (n + 1) * (univ : Finset (Perm (Fin n))).card := by
  rw [card_eq_sum_fibras (n + 1) (Fin.last n)]
  have h : ∀ i, (fibra (n + 1) (Fin.last n) i).card = (univ : Finset (Perm (Fin n))).card := by
    intro i
    rw [card_fibra_simetria (n + 1) (Fin.last n) i (Fin.last n) (Fin.last n),
      ← card_lam_eq_card_fibra, card_lam_eq_card_perm]
  simp only [h, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- `|S_n| = n!` para todo `n ≥ 1` (indução a partir de `|S_1| = 1`). -/
public theorem card_perm_eq_factorial (n : ℕ) (hn : 1 ≤ n) :
    (univ : Finset (Perm (Fin n))).card = n.factorial := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [Finset.card_univ, Nat.factorial_one, Fintype.card_eq_one_iff]
    exact ⟨1, fun σ => Equiv.ext fun x => Subsingleton.elim _ _⟩
  | succ n _ ih => rw [card_succ, ih, Nat.factorial_succ]
