/-- A context-dependent filler is the general form shared by defaults and duplicated variables. -/
theorem dependencyPruningWithFillers
    {Γ : Type} {X Y A : Γ → Type}
    (fillX : (γ : Γ) → X γ) (fillY : (γ : Γ) → Y γ)
    (e : (γ : Γ) → X γ → A γ) (e₂ : (γ : Γ) → Y γ → A γ)
    (h : ∀ γ x y, e γ x = e₂ γ y) :
    ∃ e₃ : (γ : Γ) → A γ,
      (∀ γ x, e γ x = e₃ γ) ∧ (∀ γ y, e₂ γ y = e₃ γ) := by
  let e₃ := fun γ ↦ e γ (fillX γ)
  refine ⟨e₃, ?_, ?_⟩
  · intro γ x
    exact (h γ x (fillY γ)).trans (h γ (fillX γ) (fillY γ)).symm
  · intro γ y
    exact (h γ (fillX γ) y).symm

/--
If two terms depend on disjoint extensions of a common context and their weakenings are equal,
they factor through a term in the common context. Inhabitants give constant fillers for the
coordinates discarded by dependency pruning.
-/
theorem dependencyPruning
    {Γ X Y A : Type} [Inhabited X] [Inhabited Y]
    (e : Γ → X → A) (e₂ : Γ → Y → A)
    (h : (fun γ x (_ : Y) ↦ e γ x) = fun γ (_ : X) y ↦ e₂ γ y) :
    ∃ e₃ : Γ → A,
      (fun γ x (_ : Y) ↦ e γ x) = (fun γ (_ : X) (_ : Y) ↦ e₃ γ) ∧
      (fun γ (_ : X) y ↦ e₂ γ y) = (fun γ (_ : X) (_ : Y) ↦ e₃ γ) := by
  let e₃ := fun γ ↦ e γ default
  refine ⟨e₃, ?_, ?_⟩
  · funext γ x y
    exact (congrFun (congrFun (congrFun h γ) x) default).trans
      (congrFun (congrFun (congrFun h γ) default) default).symm
  · funext γ x y
    exact (congrFun (congrFun (congrFun h γ) default) y).symm

/-- Empty private contexts show that dependency pruning has no unrestricted MLTT rule. -/
theorem dependencyPruningNotUnrestricted :
    ¬(∀ (X Y A : Type) (e : X → A) (e₂ : Y → A),
      ((fun x (_ : Y) ↦ e x) = fun (_ : X) y ↦ e₂ y) → Nonempty A) := by
  intro unrestricted
  let emptyMap : Empty → Empty := fun x ↦ nomatch x
  have h : (fun x y ↦ emptyMap x) = (fun x y ↦ emptyMap y) := by
    funext x
    exact nomatch x
  obtain ⟨value⟩ := unrestricted Empty Empty Empty emptyMap emptyMap h
  exact nomatch value
