(** Finite dependence of the semantics.  If two valuations agree on a set
    [V] of variables containing those of a command, the command gives the
    same mass to every event determined by [V].  Integrals of functions
    determined by [V] decompose over the (finitely many) classes of [V]. *)
From Stdlib Require Import Reals List.
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum interval_inference.
From mathcomp Require Import boolp classical_sets functions reals topology.
From mathcomp Require Import ereal normedtype sequences esum measure numfun.
From mathcomp Require Import measurable_realfun lebesgue_measure lebesgue_integral.
From mathcomp Require Import kernel Rstruct Rstruct_topology.
Require Import MeasureIntegration CoinLaw PHL.
Require Import Soundness.StateFacts Soundness.CommandFacts Soundness.LoopFacts
  Soundness.IntegralBounds.
Require Import Completeness.FiniteDomain.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports ValuationSpace CommandSemantics.
Local Notation real := [the realType of (Rdefinitions.R : Type)].
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section ListSums.
Context {X : Type}.

Fixpoint lsum_e (l : list X) (f : X -> \bar real) : \bar real :=
  match l with
  | nil => 0
  | cons x l' => f x + lsum_e l' f
  end.

Lemma lsum_e_ge0 l f : (forall x, List.In x l -> 0 <= f x) -> 0 <= lsum_e l f.
Proof.
elim: l => [|x l IH] h //=; apply: adde_ge0; first exact: (h x (or_introl erefl)).
by apply: IH => y hy; apply: h; exact: or_intror.
Qed.

Lemma lsum_e_ext l f g : (forall x, List.In x l -> f x = g x) -> lsum_e l f = lsum_e l g.
Proof.
elim: l => [|x l IH] h //=; rewrite (h x (or_introl erefl)) IH //.
by move=> y hy; apply: h; exact: or_intror.
Qed.

Lemma lsum_e_zero l f : (forall x, List.In x l -> f x = 0) -> lsum_e l f = 0.
Proof. by move=> h; rewrite (lsum_e_ext (g := fun _ => 0)) //; elim: l {h} => //= x l ->; rewrite adde0. Qed.

(** A sum with a single possibly nonzero term. *)
Lemma lsum_e_single l f x0 : NoDup l -> List.In x0 l ->
  (forall x, List.In x l -> x <> x0 -> f x = 0) -> lsum_e l f = f x0.
Proof.
elim: l => [|x l IH] hnd hin h //=.
inversion hnd as [|? ? hx hnd']; subst.
case: hin => [hx0 | hin].
- subst x0. rewrite lsum_e_zero ?adde0 // => y hy; apply: h; first exact: or_intror.
  by move=> e; subst y; exact: hx hy.
- have IH' := IH hnd' hin (fun y hy hne => h y (or_intror hy) hne).
  have hx0 : x <> x0 by move=> e; subst x; exact: hx hin.
  by rewrite IH' (h x (or_introl erefl) hx0) add0e.
Qed.

End ListSums.

Section ClassIntegrals.
Context {D : Domain} (FD : FiniteDomain D).
Local Notation Valuation := (@Valuation D).
Local Notation carrier := (@StateMeasure.carrier D).
Local Notation classes := (classes FD).
Local Notation class_formula := (class_formula FD).
Local Notation class_nonempty := (class_nonempty FD).

(** Events and functions determined by [V]. *)
Definition vinv (V : list Var) (A : set Valuation) : Prop :=
  forall w w', agree V w w' -> A w -> A w'.

Definition finv (V : list Var) (f : Valuation -> \bar real) : Prop :=
  forall w w', agree V w w' -> f w = f w'.

Lemma vinv_formula V g : List.incl (cformula_vars g) V -> vinv V (formula_assertion g).
Proof. by move=> hi w w' h hw; exact: (proj1 (satisfies_agree V g w w' hi h) hw). Qed.

Lemma vinv_class V a : List.In a (classes V) -> vinv V (formula_assertion (class_formula a)).
Proof. by move=> ha; apply: vinv_formula; exact: (class_formula_vars_classes FD V a ha). Qed.

Lemma vinv_iff V (A : set Valuation) w w' : vinv V A -> agree V w w' -> (A w <-> A w').
Proof. by move=> h hw; split; apply: h => //; exact: (agree_sym V w w' hw). Qed.

(** The value of [f] on a nonempty class, through a chosen representative. *)
Definition class_value (f : Valuation -> \bar real) (a : @Assignment D) : \bar real :=
  match pselect (class_nonempty a) with
  | left H => f (proj1_sig (cid H))
  | right _ => 0
  end.

Lemma class_value_spec V f a w : finv V f -> List.In a (classes V) ->
  satisfies w (class_formula a) -> class_value f a = f w.
Proof.
move=> hf ha hw; rewrite /class_value; case: pselect => [H | n].
- case: (cid H) => w0 hw0 /=; apply: hf; exact: (classes_agree FD V a w0 w ha hw0 hw).
- by exfalso; apply: n; exists w.
Qed.

Lemma integral_lsum_indic (mu : carrier) (l : list (@Assignment D)) (c : @Assignment D -> \bar real)
    (A : @Assignment D -> set Valuation) :
  (forall a, 0 <= c a) ->
  \int[mu]_v lsum_e l (fun a => c a * (\1_(A a) v)%:E) = lsum_e l (fun a => c a * mu (A a)).
Proof.
move=> c0; elim: l => [|a l IH] /=; first by rewrite integral0.
rewrite (ge0_integralD _ measurableT); cbv beta;
  try (by move=> v _; apply: lsum_e_ge0 => b _; apply: mule_ge0; rewrite ?lee_fin);
  try (by move=> v _; apply: mule_ge0; rewrite ?lee_fin);
  try exact: (@measurable_from_valuation D _ _ _).
rewrite IH; congr (_ + _).
have f0 : forall v, [set: Valuation] v -> 0 <= (\1_(A a) v : real)%:E by move=> v _; rewrite lee_fin.
have mf : measurable_fun [set: Valuation] (fun v : Valuation => (\1_(A a) v : real)%:E).
  exact: (@measurable_from_valuation D _ _ _).
rewrite (ge0_integralZl mu measurableT mf f0 (c0 a)); congr (_ * _).
by rewrite integral_indic ?setIT//; exact: all_measurable.
Qed.

(** Integrals of functions determined by [V] are finite sums over classes. *)
Lemma integral_classes V (mu : carrier) (f : Valuation -> \bar real) :
  finv V f -> (forall v, 0 <= f v) ->
  \int[mu]_v f v =
  lsum_e (classes V) (fun a => class_value f a * mu (formula_assertion (class_formula a))).
Proof.
move=> hf f0.
have cv0 a : 0 <= class_value f a by rewrite /class_value; case: pselect.
rewrite -(@integral_lsum_indic mu _ _ (fun a => formula_assertion (class_formula a)) cv0).
apply: eq_integral => v _.
have hz : forall a, List.In a (classes V) -> a <> assignment_of V v ->
    class_value f a * (\1_(formula_assertion (class_formula a)) v)%:E = 0.
  move=> a ha hne; rewrite indicE memNset ?mule0 //.
  by move=> hv; apply: hne; exact: (classes_member FD V a v ha hv).
rewrite (lsum_e_single (classes_nodup FD V) (classes_own FD V v) hz).
rewrite (class_value_spec hf (classes_own FD V v) (satisfies_own_class FD V v)).
by rewrite indicE mem_set ?mule1 //; exact: (satisfies_own_class FD V v).
Qed.

Lemma integral_classes_eq V (mu nu : carrier) (f : Valuation -> \bar real) :
  finv V f -> (forall v, 0 <= f v) ->
  (forall a, List.In a (classes V) ->
     mu (formula_assertion (class_formula a)) = nu (formula_assertion (class_formula a))) ->
  \int[mu]_v f v = \int[nu]_v f v.
Proof.
move=> hf f0 h; rewrite (integral_classes mu hf f0) (integral_classes nu hf f0).
by apply: lsum_e_ext => a ha; rewrite h.
Qed.

End ClassIntegrals.

Section Dependence.
Context {D : Domain} (FD : FiniteDomain D).
Local Notation Valuation := (@Valuation D).
Local Notation Kernel := (@Kernel D).
Local Notation vinv := (@vinv D).

(** A kernel respects [V] if agreeing inputs give equal masses to events
    determined by [V]. *)
Definition kinv (V : list Var) (k : Kernel) : Prop :=
  forall w w' A, agree V w w' -> vinv V A -> k w A = k w' A.

Lemma kinv_integral V (k : Kernel) w w' (f : Valuation -> \bar real) :
  kinv V k -> agree V w w' -> finv V f -> (forall v, 0 <= f v) ->
  \int[k w]_v f v = \int[k w']_v f v.
Proof.
move=> hk hw hf f0; apply: (@integral_classes_eq D FD V (k w) (k w') f hf f0) => a ha.
by apply: hk => //; exact: vinv_class.
Qed.

Lemma dirac_vinv V (A : set Valuation) (w w' : Valuation) :
  vinv V A -> agree V w w' -> (\d_w A : \bar real) = \d_w' A.
Proof.
move=> hA hw; rewrite !diracE.
case: (pselect (A w)) => h.
- by rewrite !mem_set //; apply: hA h.
- by rewrite !memNset // => h'; apply: h; apply: hA h'; exact: (agree_sym V w w' hw).
Qed.

Lemma kinv_skip V : kinv V [the real.-spker _ ~> _ of @skip D].
Proof.
move=> w w' A hw hA.
change ((\d_(w : Valuation) A : \bar real) = \d_(w' : Valuation) A).
exact: (dirac_vinv hA hw).
Qed.

Lemma kinv_dom_assign V x t : List.incl (term_vars t) V ->
  kinv V [the real.-spker _ ~> _ of @dom_assign D x t].
Proof.
move=> ht w w' A hw hA.
change ((\d_(update_dom w x (term_eval t w) : Valuation) A : \bar real) =
        \d_(update_dom w' x (term_eval t w') : Valuation) A).
apply: (dirac_vinv hA).
rewrite (term_eval_agree V t w w' ht hw); exact: (agree_update_dom V w w' x _ hw).
Qed.

Lemma kinv_bool_assign V b g : List.incl (cformula_vars g) V ->
  kinv V [the real.-spker _ ~> _ of @bool_assign D b g].
Proof.
move=> hg w w' A hw hA.
change ((\d_(update_bool w b (cformula_eval_bool g w) : Valuation) A : \bar real) =
        \d_(update_bool w' b (cformula_eval_bool g w') : Valuation) A).
apply: (dirac_vinv hA).
rewrite (eval_bool_agree V g w w' hg hw); exact: (agree_update_bool V w w' b _ hw).
Qed.

Lemma indic_vinv V (A : set Valuation) (w w' : Valuation) :
  vinv V A -> agree V w w' -> (\1_A w : real) = \1_A w'.
Proof.
move=> hA hw; rewrite !indicP.
destruct (pselect (A w)) as [h|h]; destruct (pselect (A w')) as [h'|h'] => //.
- by exfalso; apply: h'; apply: hA h.
- by exfalso; apply: h; apply: hA h'; exact: (agree_sym V w w' hw).
Qed.

Lemma kinv_toss V b r : kinv V [the real.-spker _ ~> _ of @toss D b r].
Proof.
move=> w w' A hw hA.
case hr: (CoinLaw.toss_valid r).
- rewrite !toss_event_valid //.
  by rewrite (indic_vinv hA (agree_update_bool V w w' b true hw))
             (indic_vinv hA (agree_update_bool V w w' b false hw)).
- by rewrite !toss_invalid ?hr.
Qed.

Lemma kinv_sequence V (k l : Kernel) : kinv V k -> kinv V l ->
  kinv V [the real.-spker _ ~> _ of @sequence D k l].
Proof.
move=> hk hl w w' A hw hA; rewrite !sequence_event.
apply: (kinv_integral hk hw).
- by move=> z z' hz; apply: hl.
- by move=> z; exact: measure_ge0.
Qed.

Lemma kinv_branch V g (k l : Kernel) : List.incl (cformula_vars g) V -> kinv V k -> kinv V l ->
  kinv V [the real.-spker _ ~> _ of @branch D g k l].
Proof.
move=> hg hk hl w w' A hw hA.
change ((if cformula_eval_bool g w then k w else l w) A =
        (if cformula_eval_bool g w' then k w' else l w') A).
rewrite (eval_bool_agree V g w w' hg hw); case: (cformula_eval_bool g w'); [exact: hk | exact: hl].
Qed.

Lemma kinv_zero V : kinv V [the real.-spker _ ~> _ of @zero D].
Proof. by []. Qed.

Lemma kinv_loop_exit V g (k : Kernel) n : List.incl (cformula_vars g) V -> kinv V k ->
  kinv V (loop_exit g k n).
Proof.
move=> hg hk; elim: n => [|n IH] /=.
- apply: kinv_branch; [exact: hg | exact: kinv_zero | exact: kinv_skip].
- apply: kinv_branch; [exact: hg | exact: kinv_sequence | exact: kinv_zero].
Qed.

Lemma kinv_loop V g (k : Kernel) : List.incl (cformula_vars g) V -> kinv V k ->
  kinv V [the real.-spker _ ~> _ of @loop D g k].
Proof.
move=> hg hk w w' A hw hA; rewrite !loop_event.
by apply: eq_eseriesr => n _; apply: (kinv_loop_exit n hg hk).
Qed.

(** The dependence lemma for every command. *)
Theorem kinv_denote V (c : Cmd D) : List.incl (cmd_vars c) V -> kinv V (CommandSemantics.denote c).
Proof.
elim: c => [|x t|b g|b r|c1 IH1 c2 IH2|g c1 IH1 c2 IH2|g c IH] /= hi.
- exact: kinv_skip.
- by apply: kinv_dom_assign => v hv; apply: hi; right.
- by apply: kinv_bool_assign => v hv; apply: hi; right.
- exact: kinv_toss.
- apply: kinv_sequence; [apply: IH1 | apply: IH2] => v hv; apply: hi;
    rewrite List.in_app_iff; auto.
- apply: kinv_branch; [| apply: IH1 | apply: IH2] => v hv; apply: hi;
    rewrite !List.in_app_iff; auto.
- apply: kinv_loop; [| apply: IH] => v hv; apply: hi; rewrite List.in_app_iff; auto.
Qed.

End Dependence.
