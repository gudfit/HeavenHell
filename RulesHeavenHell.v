From Stdlib Require Import List Lia Arith PeanoNat Bool.
Import ListNotations.
Set Implicit Arguments.

Module HeavenHell.

  Inductive State := Glory | Gnash.

  Definition state_eqb (a b : State) : bool :=
    match a, b with
    | Glory, Glory => true
    | Gnash, Gnash => true
    | _, _ => false
    end.
    
  Definition ind (b:bool) : nat := if b then 1 else 0.
  Lemma ind_le_1 : forall b, ind b <= 1.  Proof. intro b; destruct b; cbn; lia. Qed.
  Lemma mul_ind_le : forall a b, a * ind b <= a.
  Proof. intros a b; destruct b; cbn; lia. Qed.
  Lemma state_eqb_refl (x : State) : state_eqb x x = true.
  Proof. destruct x; reflexivity. Qed.


  (* ---------- Generic finite graph setting ---------- *)

  Section Generic.

    Variable V : Type.
    Variable dec : forall x y:V, {x=y}+{x<>y}.
    Variable allV : list V.
    Hypothesis allV_nodup : NoDup allV.
    Hypothesis allV_complete : forall v:V, In v allV.
    
    Variable w : V -> V -> nat.

    Definition sum_all (f:V->nat) : nat :=
      fold_right Nat.add 0 (map f allV).

    Definition statef := V -> State.
    Definition score (s:statef) (x:State) (v:V) : nat :=
      sum_all (fun u => w u v * ind (state_eqb (s u) x)).

    Lemma fold_map_le :
      forall (l : list V) (f g : V -> nat),
        (forall u, In u l -> f u <= g u) ->
        fold_right Nat.add 0 (map f l)
        <=
        fold_right Nat.add 0 (map g l).
    Proof.
      intros l; induction l as [|a tl IH]; cbn; intros f g H.
      - lia.
      - pose proof (H a (or_introl eq_refl)) as Ha.
        assert (H' : forall u, In u tl -> f u <= g u).
        { intros u Hu; apply H; right; exact Hu. }
        specialize (IH f g H').
        apply Nat.add_le_mono; [exact Ha | exact IH].
    Qed.

    Lemma sum_all_le :
      forall (f g: V->nat),
        (forall u, In u allV -> f u <= g u) ->
        sum_all f <= sum_all g.
    Proof.
      intros f g H; unfold sum_all.
      apply (fold_map_le allV f g); exact H.
    Qed.
    
    Lemma sum_all_ge_at :
      forall (h:V->nat) (x:V), In x allV -> h x <= sum_all h.
    Proof.
      intros h x Hin.
      unfold sum_all.
      revert x Hin.
      generalize allV as l.
      intros l x Hin.
      induction l as [|a tl IH]; cbn in *.
      - contradiction.
      - destruct Hin as [->|Hin].
        + lia.
        + specialize (IH Hin). lia.
    Qed.

    Lemma sum_all_ge_at_list :
      forall (h:V->nat) (l:list V) (x:V),
        In x l -> h x <= fold_right Nat.add 0 (map h l).
    Proof.
      intros h l; induction l as [|a tl IH]; cbn; intros x Hin.
      - contradiction.
      - destruct Hin as [->|Hin].
        + lia.
        + specialize (IH x Hin). lia.
    Qed.

    Lemma sum_all_ge_at_polymorphic :
      forall (h:V->nat) (x:V), In x allV -> h x <= sum_all h.
    Proof.
      intros h x Hin.
      unfold sum_all.
      now apply (sum_all_ge_at_list h allV x).
    Qed.

    Variable g : V.
    Definition force_g (s:statef) : statef :=
      fun u => if dec u g then Glory else s u.
    Definition next_heaven (s:statef) (v:V) : State :=
      if dec v g then Glory
      else
        let s' := force_g s in
        let SG := score s' Glory v in
        let SN := score s' Gnash v in
        if Nat.ltb SG SN then Gnash else Glory.
    Definition rest_weight (v:V) : nat :=
      sum_all (fun u => if dec u g then 0 else w u v).
    Definition hub_weight (v:V) : nat := w g v.
    
    Lemma force_g_at_g s : (force_g s) g = Glory.
    Proof. unfold force_g; destruct (dec g g) as [_|H]; [reflexivity|contradiction]. Qed.


    Lemma scoreN_le_rest : forall s v,
      score (force_g s) Gnash v <= rest_weight v.
    Proof.
      intros s v.
      unfold score, rest_weight, sum_all.
      eapply sum_all_le.
      intros u Hu.
      destruct (dec u g) as [->|Hneq].
      - rewrite (force_g_at_g s). cbn. lia.
      - cbn. apply mul_ind_le.
    Qed.

    Lemma scoreG_ge_hub : forall s v,
      hub_weight v <= score (force_g s) Glory v.
    Proof.
      intros s v.
      unfold hub_weight, score.
      set (h := fun u => w u v * ind (state_eqb (force_g s u) Glory)).
      pose proof (sum_all_ge_at_polymorphic h g (allV_complete g)) as H.
      unfold h in H |- *.
      cbn.
      rewrite force_g_at_g in H.
      cbn in H.
      rewrite Nat.mul_1_r in H.
      exact H.
    Qed.
    
    Lemma scoreG_le_total : forall s v,
      score (force_g s) Glory v <= sum_all (fun u => w u v).
    Proof.
      intros s v.
      unfold score.
      eapply sum_all_le; intros u _.
      apply mul_ind_le.
    Qed.

    Definition mask_g (k: V -> nat) (u: V) : nat :=
      if dec u g then k u else 0.

    Lemma mask_g_at_g : forall k, mask_g k g = k g.
    Proof. intros k; unfold mask_g; destruct (dec g g) as [_|C]; [reflexivity|contradiction]. Qed.

    Lemma mask_g_at_neq : forall k u, u <> g -> mask_g k u = 0.
    Proof. intros k u H; unfold mask_g; destruct (dec u g) as [E|E]; [congruence|reflexivity]. Qed.

    Lemma masked_sum_zero_if_notin :
      forall k l, ~ In g l ->
        fold_right Nat.add 0 (map (mask_g k) l) = 0.
    Proof.
      intros k l Hnin.
      revert Hnin.
      induction l as [|a tl IH]; intros Hnin; cbn; [reflexivity|].
      assert (Ha  : a <> g)  by (intro E; subst; apply Hnin; left; reflexivity).
      assert (Htl : ~ In g tl) by (intro E; apply Hnin; right; exact E).
      assert (Hmask : mask_g k a = 0) by (apply mask_g_at_neq; exact Ha).
      rewrite Hmask.
      specialize (IH Htl).
      rewrite IH.
      reflexivity.
    Qed.

    Lemma masked_sum_pick_g :
      forall k l, NoDup l -> In g l ->
        fold_right Nat.add 0 (map (mask_g k) l) = k g.
    Proof.
      intros k l Hnd Hin; revert k Hin Hnd.
      induction l as [|a tl IH]; intros k Hin Hnd; [contradiction|].
      inversion Hnd as [|? ? Hnotin Hnd_tl]; subst.
      destruct Hin as [Ha|Hin_tl].
      - subst a. cbn. rewrite mask_g_at_g.
        rewrite (masked_sum_zero_if_notin k tl) by exact Hnotin. lia.
      - cbn.  assert (Ha : a <> g) by (intro E; subst; apply Hnotin; exact Hin_tl).
        assert (Hmask : mask_g k a = 0) by (apply mask_g_at_neq; exact Ha).
        rewrite Hmask.
        rewrite (IH k Hin_tl Hnd_tl).
        reflexivity.
    Qed.

    Lemma sum_all_mask_g :
      forall (k : V -> nat),
        sum_all (fun u => if dec u g then k u else 0) = k g.
    Proof.
      intros k; unfold sum_all.
      change (map (fun u => if dec u g then k u else 0) allV)
        with (map (mask_g k) allV).
      apply masked_sum_pick_g; [exact allV_nodup | apply allV_complete].
    Qed.

    Lemma fold_map_add :
      forall (l : list V) (f g0 : V -> nat),
        fold_right Nat.add 0 (map (fun u => f u + g0 u) l)
        = fold_right Nat.add 0 (map f l) + fold_right Nat.add 0 (map g0 l).
    Proof.
      intros l f g0; induction l as [|a tl IH]; cbn; [lia|].
      rewrite IH; lia.
    Qed.

    Lemma sum_all_add :
      forall (f g0 : V -> nat),
        sum_all (fun u => f u + g0 u) = sum_all f + sum_all g0.
    Proof.
      intros f g0; unfold sum_all; apply fold_map_add.
    Qed.

    Lemma sum_all_ext :
      forall (f g : V -> nat),
        (forall u, In u allV -> f u = g u) ->
        sum_all f = sum_all g.
    Proof.
      intros f g0 H; unfold sum_all.
      erewrite map_ext_in with (l:=allV).
      - reflexivity.
      - intros u Hu; apply H; exact Hu.
    Qed.

    Lemma if_split_add_nat :
      forall (b:bool) x y, (if b then x else y) = (if b then x else 0) + (if b then 0 else y).
    Proof. intros []; lia. Qed.

    Lemma scoreG_integrand_pointwise :
      forall s v u,
        w u v * ind (state_eqb (force_g s u) Glory)
        =
        (if dec u g then w u v else w u v * ind (state_eqb (s u) Glory)).
    Proof.
      intros s v u.
      unfold force_g.
      destruct (dec u g) as [E|E]; cbn; [lia|reflexivity].
    Qed.
    
    Lemma if_split_add_sumbool_nat :
      forall (P:Prop) (d:{P}+{~P}) x y,
        (if d then x else y) = (if d then x else 0) + (if d then 0 else y).
    Proof. intros P d x y; destruct d; cbn; lia. Qed.

    Lemma scoreG_integrand_split :
      forall s v u,
        w u v * ind (state_eqb (force_g s u) Glory)
        =
        (if dec u g then w u v else 0)
        +
        (if dec u g then 0 else w u v * ind (state_eqb (s u) Glory)).
    Proof.
      intros s v u.
      rewrite scoreG_integrand_pointwise.
      apply if_split_add_sumbool_nat.
    Qed.
    
    Lemma scoreG_split :
      forall s v,
        score (force_g s) Glory v
        = hub_weight v
          + sum_all (fun u =>
              if dec u g then 0
              else w u v * ind (state_eqb (s u) Glory)).
    Proof.
      intros s v.
      unfold score, hub_weight.
      transitivity
        (sum_all (fun u =>
          (if dec u g then w u v else 0) +
          (if dec u g then 0 else w u v * ind (state_eqb (s u) Glory)))).
      - apply sum_all_ext; intros u _.
        apply scoreG_integrand_split.
      - rewrite (sum_all_add
          (fun u => if dec u g then w u v else 0)
          (fun u => if dec u g then 0 else w u v * ind (state_eqb (s u) Glory))).
        rewrite (sum_all_mask_g (fun u => w u v)).
        reflexivity.
    Qed.

    Lemma total_weight_split :
      forall v,
        sum_all (fun u => w u v) = hub_weight v + rest_weight v.
    Proof.
      intro v.
      unfold hub_weight, rest_weight.
      transitivity
        (sum_all (fun u => if dec u g then w u v else 0)
         + sum_all (fun u => if dec u g then 0 else w u v)).
      { rewrite <- (sum_all_add
            (fun u => if dec u g then w u v else 0)
            (fun u => if dec u g then 0 else w u v)).
        apply sum_all_ext; intros u _.
        destruct (dec u g); lia. }
      rewrite (sum_all_mask_g (fun u => w u v)).
      reflexivity.
    Qed.

    Definition all_gnash : statef := fun _ => Gnash.

    Lemma fold_sum_map_zero {A} (l : list A) :
      fold_right Nat.add 0 (map (fun _ : A => 0) l) = 0.
    Proof.
      induction l as [|a tl IH]; cbn; [reflexivity|exact IH].
    Qed.

    Lemma scoreG_all_gnash_eq_hub :
      forall v,
        score (force_g all_gnash) Glory v = hub_weight v.
    Proof.
      intro v.
      rewrite (scoreG_split all_gnash v).
      assert (Hsum :
        sum_all (fun u =>
                   if dec u g then 0
                   else w u v * ind (state_eqb (all_gnash u) Glory))
        = sum_all (fun _ => 0)).
      { apply sum_all_ext. intros u _.
        destruct (dec u g); cbn; [reflexivity|].
        now rewrite Nat.mul_0_r. }
      rewrite Hsum.
      unfold sum_all.
      rewrite (@fold_sum_map_zero V allV).
      lia.
    Qed.

    Lemma scoreN_all_gnash_eq_rest :
      forall v,
        score (force_g all_gnash) Gnash v = rest_weight v.
    Proof.
      intro v.
      unfold rest_weight, score, all_gnash, force_g.
      eapply sum_all_ext. intros u _.
      destruct (dec u g); cbn; lia.
    Qed.
    
    Lemma next_heaven_at_g s : next_heaven s g = Glory.
    Proof.
      unfold next_heaven. destruct (dec g g) as [_|C]; [reflexivity|contradiction].
    Qed.

    Lemma next_heaven_eq_Glory_iff_not_g :
      forall s v,
        v <> g ->
        (next_heaven s v = Glory
         <-> score (force_g s) Gnash v <= score (force_g s) Glory v).
    Proof.
      intros s v Hvg.
      unfold next_heaven.
      destruct (dec v g) as [E|E]; [contradiction|].
      set (s' := force_g s).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash v).
      split.
      - intro H.
        destruct (Nat.ltb SG SN) eqn:Hlt; cbn in H; [discriminate|].
        apply Nat.ltb_ge in Hlt; exact Hlt.
      - intro Hle.
        destruct (Nat.ltb SG SN) eqn:Hlt; cbn; [apply Nat.ltb_lt in Hlt; lia|reflexivity].
    Qed.

    Lemma bounds_force_g :
      forall s v,
        score (force_g s) Gnash v <= rest_weight v
        /\ hub_weight v <= score (force_g s) Glory v.
    Proof.
      intros s v. split; [apply scoreN_le_rest | apply scoreG_ge_hub].
    Qed.

    Lemma domination_implies_glory :
      forall s v,
        v <> g ->
        rest_weight v <= hub_weight v ->
        next_heaven s v = Glory.
    Proof.
      intros s v Hvg Hdom.
      unfold next_heaven.
      destruct (dec v g) as [|Hg]; [contradiction|].
      set (s' := force_g s).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash v).
      destruct (Nat.ltb SG SN) eqn:Hlt.
      - apply Nat.ltb_lt in Hlt.
        destruct (bounds_force_g s v) as [Hsn_le_rest Hhub_le_SG].
        change (score (force_g s) Gnash v) with SN in Hsn_le_rest.
        change (score (force_g s) Glory v) with SG in Hhub_le_SG.
        pose proof (Nat.lt_le_trans _ _ _ Hlt Hsn_le_rest) as H1.
        pose proof (Nat.lt_le_trans _ _ _ H1  Hdom)        as H2.
        pose proof (Nat.lt_le_trans _ _ _ H2  Hhub_le_SG)  as H3.
        now apply (Nat.lt_irrefl _) in H3.
      - reflexivity.
    Qed.

    Lemma all_gnash_glory_iff_domination :
      forall v,
        v <> g ->
        (next_heaven all_gnash v = Glory <-> hub_weight v >= rest_weight v).
    Proof.
      intros v Hvg.
      unfold next_heaven.
      destruct (dec v g) as [|_]; [contradiction|].
      rewrite scoreG_all_gnash_eq_hub, scoreN_all_gnash_eq_rest.
      split.
      - intro H; destruct (Nat.ltb (hub_weight v) (rest_weight v)) eqn:Hlt; cbn in H; [discriminate|].
        apply Nat.ltb_ge in Hlt; exact Hlt.
      - intro Hge; destruct (Nat.ltb (hub_weight v) (rest_weight v)) eqn:Hlt; cbn.
        + apply Nat.ltb_lt in Hlt; lia.
        + reflexivity.
    Qed.
    
    Theorem heaven_one_step_all_G_iff_domination_ge :
      (forall s v, next_heaven s v = Glory)
      <-> (forall v, v <> g -> hub_weight v >= rest_weight v).
    Proof.
      split.
      - intros Hall v Hvg.
        pose (Hiff := all_gnash_glory_iff_domination (v:=v) Hvg).
        destruct Hiff as [Hfwd _].
        apply Hfwd.
        exact (Hall all_gnash v).
      - intros Hdom s v.
        destruct (dec v g) as [->|Hvg].
        + apply next_heaven_at_g.
        + apply domination_implies_glory; [assumption|].
          exact (Hdom v Hvg).
    Qed.

    Definition list_max (l : list nat) : nat := fold_right Nat.max 0 l.

    Lemma list_max_In_le :
      forall (l:list nat) x, In x l -> x <= list_max l.
    Proof.
      induction l as [|a tl IH]; cbn; intros x Hin; [contradiction|].
      destruct Hin as [<-|Hin].
      - apply Nat.le_max_l.
      - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
    Qed.
    
    Lemma list_max_le_of_forall :
      forall (l:list nat) (W:nat),
        (forall x, In x l -> x <= W) -> list_max l <= W.
    Proof.
      induction l as [|a tl IH]; cbn; intros W Hall; [lia|].
      apply Nat.max_lub.
      - apply Hall; left; reflexivity.
      - apply IH; intros x Hx; apply Hall; right; exact Hx.
    Qed.
    
    Lemma list_max_gt_ex :
      forall (l:list nat) (W:nat),
        list_max l > W -> exists x, In x l /\ x > W.
    Proof.
      induction l as [|a tl IH]; cbn; intros W H; [lia|].
      apply Nat.max_lt_iff in H as [Ha|Ht].
      - exists a; split; [left; reflexivity|exact Ha].
      - destruct (IH W Ht) as [x [Hx Hgt]].
        exists x; split; [right; exact Hx|exact Hgt].
    Qed.

    Definition is_nonhub (u:V) : bool := if dec u g then false else true.
    Definition nonhubs : list V := filter is_nonhub allV.
    Definition max_rest : nat := list_max (map rest_weight nonhubs).
    Definition indeg_nonhub (v:V) : nat := sum_all (fun u => if dec u g then 0 else ind (0 <? w u v)).
    Definition max_in_nonhub (v:V) : nat := list_max (map (fun u => if dec u g then 0 else w u v) allV).

    Lemma fold_map_mul_const :
      forall (l:list V) (h:V->nat) c,
        fold_right Nat.add 0 (map (fun u => c * h u) l)
        = c * fold_right Nat.add 0 (map h l).
    Proof.
      intros l h c. induction l as [|a tl IH]; simpl.
      - now rewrite Nat.mul_0_r.
      - rewrite IH. rewrite Nat.mul_add_distr_l. reflexivity.
    Qed.

    Lemma sum_all_mul_const :
      forall (h:V->nat) c, sum_all (fun u => c * h u) = c * sum_all h.
    Proof.
      intros h c. unfold sum_all. apply fold_map_mul_const.
    Qed.

    Lemma w_le_max_in_nonhub :
      forall v u, (if dec u g then 0 else w u v) <= max_in_nonhub v.
    Proof.
      intros v u.
      unfold max_in_nonhub.
      apply list_max_In_le.
      apply in_map_iff; exists u; split; [reflexivity|apply allV_complete].
    Qed.

    Lemma le_to_le_mul_ind_ltb0 :
      forall n M, n <= M -> n <= M * ind (0 <? n).
    Proof.
      intros n M Hle. destruct n as [|n']; cbn; [lia|].
      lia.
    Qed.

    Lemma rest_term_le :
      forall v u,
        (if dec u g then 0 else w u v)
        <= max_in_nonhub v * (if dec u g then 0 else ind (0 <? w u v)).
    Proof.
      intros v u.
      destruct (dec u g) as [->|Hug]; cbn; [lia|].
      apply le_to_le_mul_ind_ltb0.
      pose proof (w_le_max_in_nonhub v u) as Hw.
      destruct (dec u g) as [Eg|_].
      - exfalso; apply Hug; exact Eg.
      - simpl in Hw; exact Hw.
    Qed.

    Lemma rest_le_indeg_times_max :
      forall v,
        rest_weight v <= indeg_nonhub v * max_in_nonhub v.
    Proof.
      intro v.
      unfold rest_weight, indeg_nonhub.
      set (M := max_in_nonhub v).
      eapply Nat.le_trans
        with (m := sum_all (fun u => M * (if dec u g then 0 else ind (0 <? w u v)))).
      - eapply (sum_all_le
                  (fun u => if dec u g then 0 else w u v)
                  (fun u => M * (if dec u g then 0 else ind (0 <? w u v)))).
        intros u _; apply rest_term_le.
      - rewrite sum_all_mul_const. 
        rewrite Nat.mul_comm. 
        reflexivity.
    Qed.

    Definition indeg_global : nat := list_max (map indeg_nonhub nonhubs).
    Definition wmax_global  : nat := list_max (map max_in_nonhub nonhubs).

    Lemma indeg_nonhub_le_global :
      forall v, In v nonhubs -> indeg_nonhub v <= indeg_global.
    Proof.
      intros v Hv. unfold indeg_global.
      apply list_max_In_le. apply in_map. exact Hv.
    Qed.

    Lemma max_in_nonhub_le_global :
      forall v, In v nonhubs -> max_in_nonhub v <= wmax_global.
    Proof.
      intros v Hv. unfold wmax_global.
      apply list_max_In_le. apply in_map. exact Hv.
    Qed.

    Lemma max_rest_le_degmax :
      max_rest <= indeg_global * wmax_global.
    Proof.
      unfold max_rest.
      eapply list_max_le_of_forall.
      intros x Hx.
      apply in_map_iff in Hx as [v [Hv Hx]].
      subst x.
      pose proof (rest_le_indeg_times_max v) as Hrest.
      pose proof (indeg_nonhub_le_global v Hx) as Hdeg.
      pose proof (max_in_nonhub_le_global v Hx) as Hwmax.
      eapply Nat.le_trans; [exact Hrest|].
      eapply Nat.le_trans with (m := indeg_global * max_in_nonhub v).
      - apply Nat.mul_le_mono_r, Hdeg.
      - apply Nat.mul_le_mono_l. exact Hwmax.
    Qed.

    Corollary uniform_hub_one_step_sufficient_degmax :
      forall W, (forall v, v <> g -> hub_weight v = W) ->
      W >= indeg_global * wmax_global ->
      (forall s v, next_heaven s v = Glory).
    Proof.
      intros W Hunif HW.
      apply (proj2 heaven_one_step_all_G_iff_domination_ge).
      intros v Hvg.
      rewrite Hunif by exact Hvg.
      assert (Hmax : max_rest <= W)
        by (eapply Nat.le_trans; [apply max_rest_le_degmax | exact HW]).
      assert (Hin : In v nonhubs).
      { unfold nonhubs, is_nonhub.
        apply filter_In; split.
        - apply allV_complete.
        - destruct (dec v g) as [Eg|NE]; [exfalso; apply Hvg; exact Eg|reflexivity]. }
      assert (Hrest_le_max : rest_weight v <= max_rest).
      { unfold max_rest.
        apply list_max_In_le.
        apply in_map; exact Hin. }
      eapply Nat.le_trans; [exact Hrest_le_max | exact Hmax].
    Qed.

    Lemma nonhubs_In_iff :
      forall v, In v nonhubs <-> In v allV /\ v <> g.
    Proof.
      intro v; unfold nonhubs, is_nonhub.
      rewrite filter_In; split; intros [Hin Hp]; split; try exact Hin.
      - destruct (dec v g) as [E|NE]; cbn in Hp; [discriminate|assumption].
      - destruct (dec v g) as [E|NE]; [congruence|reflexivity].
    Qed.

    Lemma rest_le_max_rest :
      forall v, v <> g -> rest_weight v <= max_rest.
    Proof.
      intros v Hvg.
      assert (Hin : In v nonhubs).
      { apply nonhubs_In_iff; split; [apply allV_complete|assumption]. }
      unfold max_rest.
      apply list_max_In_le.
      apply in_map; exact Hin.
    Qed.

    Lemma max_rest_le_iff :
      forall W, max_rest <= W <-> (forall v, v <> g -> rest_weight v <= W).
    Proof.
      intro W; split.
      - intros H v Hvg.
        eapply Nat.le_trans; [apply rest_le_max_rest; exact Hvg|assumption].
      - intros H.
        unfold max_rest.
        eapply list_max_le_of_forall.
        intros x Hx.
        apply in_map_iff in Hx as [v [Hin Hxeq]].
        rewrite <- Hin.
        apply nonhubs_In_iff in Hxeq as [_ Hvg].
        exact (H v Hvg).
    Qed.
    
    Variable W : nat.
    Hypothesis hub_uniform : forall v, v <> g -> hub_weight v = W.
    
    Theorem uniform_hub_one_step_iff : (forall s v, next_heaven s v = Glory) <-> W >= max_rest.
    Proof.
      rewrite (heaven_one_step_all_G_iff_domination_ge).
      split.
      - intros Hdom.
        apply (proj2 (max_rest_le_iff W)).
        intros v Hvg.
        specialize (Hdom v Hvg).
        rewrite hub_uniform in Hdom by exact Hvg.
        exact Hdom.
      - intros HW v Hvg; rewrite hub_uniform by exact Hvg. 
        exact ((proj1 (max_rest_le_iff W) HW) v Hvg).
    Qed.

    Lemma in_nonhubs_not_g : forall v, In v nonhubs -> v <> g.
    Proof.
      intros v Hv. apply nonhubs_In_iff in Hv as [_ Hvg]. exact Hvg.
    Qed.

    Lemma max_rest_gt_ex_v :
      forall W, W < max_rest -> exists v, In v nonhubs /\ rest_weight v > W.
    Proof.
      intros W0 Hlt.
      unfold max_rest in Hlt.
      assert (Hlt' : list_max (map rest_weight nonhubs) > W0) by lia.
      eapply list_max_gt_ex in Hlt'.
      destruct Hlt' as [x [Hx Hgt]].
      apply in_map_iff in Hx as [v [Hin Heq]].
      exists v; split; [exact Heq|].
      rewrite Hin. exact Hgt.
    Qed.

    Lemma gnash_on_all_gnash_if_hub_lt_rest :
      forall v, v <> g -> hub_weight v < rest_weight v -> next_heaven all_gnash v = Gnash.
    Proof.
      intros v Hvg Hlt.
      unfold next_heaven.
      destruct (dec v g) as [Eg|Eg]; [contradiction|].
      rewrite scoreG_all_gnash_eq_hub, scoreN_all_gnash_eq_rest.
      apply Nat.ltb_lt in Hlt. now rewrite Hlt.
    Qed.

    Theorem uniform_hub_below_threshold_counterexample :
      W < max_rest ->
      exists v, v <> g /\ next_heaven all_gnash v = Gnash.
    Proof.
      intro Hlt.
      eapply (max_rest_gt_ex_v (W:=W)) in Hlt.
      destruct Hlt as [v [Hv_in Hrest_gt]].
      apply nonhubs_In_iff in Hv_in as [_ Hvg].
      assert (Hhub_lt_rest : hub_weight v < rest_weight v).
      { rewrite hub_uniform by exact Hvg. lia. }
      exists v; split; [exact Hvg|].
      apply (gnash_on_all_gnash_if_hub_lt_rest (v:=v)); [exact Hvg | exact Hhub_lt_rest].
    Qed.
    
    Variable tau : V -> nat.
    
    Definition next_heaven_tau (s:statef) (v:V) : State :=
      if dec v g then Glory
      else
        let s' := force_g s in
        let SG := score s' Glory v in
        let SN := score s' Gnash  v in
        if Nat.ltb (SG + tau v) SN then Gnash else Glory.
        
    Lemma next_heaven_tau_at_g s : next_heaven_tau s g = Glory.
    Proof.
      unfold next_heaven_tau. destruct (dec g g); [reflexivity|contradiction].
    Qed.
    
    Lemma next_heaven_tau_eq_Glory_iff_not_g :
      forall s v,
        v <> g ->
        (next_heaven_tau s v = Glory
         <-> score (force_g s) Gnash v
             <= score (force_g s) Glory v + tau v).
    Proof.
      intros s v Hvg.
      unfold next_heaven_tau.
      destruct (dec v g) as [E|E]; [contradiction|].
      set (s' := force_g s).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash  v).
      split.
      - intro HG.
        destruct (Nat.ltb (SG + tau v) SN) eqn:Hlt; [discriminate|].
        apply Nat.ltb_ge in Hlt. exact Hlt.
      - intro Hle.
        destruct (Nat.ltb (SG + tau v) SN) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|reflexivity].
    Qed.

    Lemma domination_tau_implies_glory :
      forall s v,
        v <> g ->
        rest_weight v <= hub_weight v + tau v ->
        next_heaven_tau s v = Glory.
    Proof.
      intros s v Hvg Hdom.
      unfold next_heaven_tau.
      destruct (dec v g) as [|Hg]; [contradiction|].
      set (s' := force_g s).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash  v).
      destruct (Nat.ltb (SG + tau v) SN) eqn:Hlt.
      - apply Nat.ltb_lt in Hlt.
        destruct (bounds_force_g s v) as [Hsn_le_rest Hhub_le_SG].
        change (score (force_g s) Gnash v) with SN in Hsn_le_rest.
        change (score (force_g s) Glory v) with SG in Hhub_le_SG.
        assert (H1 : SN <= hub_weight v + tau v)
          by (eapply Nat.le_trans; [exact Hsn_le_rest|exact Hdom]).
        assert (H2 : hub_weight v + tau v <= SG + tau v) by lia.
        assert (Hcontr : SG + tau v < SG + tau v)
          by (eapply Nat.lt_le_trans; [exact Hlt|];
            eapply Nat.le_trans; [exact H1|exact H2]).
        exfalso. now apply Nat.lt_irrefl in Hcontr.
      - reflexivity.
    Qed.

    Lemma all_gnash_glory_iff_domination_tau :
      forall v,
        v <> g ->
        (next_heaven_tau all_gnash v = Glory
         <-> hub_weight v + tau v >= rest_weight v).
    Proof.
      intros v Hvg.
      unfold next_heaven_tau.
      destruct (dec v g) as [|_]; [contradiction|].
      rewrite scoreG_all_gnash_eq_hub, scoreN_all_gnash_eq_rest.
      split.
      - intro HG.
        destruct (Nat.ltb (hub_weight v + tau v) (rest_weight v)) eqn:Hlt; [discriminate|].
        apply Nat.ltb_ge in Hlt. exact Hlt.
      - intro Hge.
        destruct (Nat.ltb (hub_weight v + tau v) (rest_weight v)) eqn:Hlt.
        + apply Nat.ltb_lt in Hlt; lia.
        + reflexivity.
    Qed.
    
    Theorem heaven_one_step_all_G_iff_domination_ge_tau :
      (forall s v, next_heaven_tau s v = Glory)
      <-> (forall v, v <> g -> hub_weight v + tau v >= rest_weight v).
    Proof.
      split.
      - intros Hall v Hvg.
        specialize (Hall all_gnash v).
        unfold next_heaven_tau in Hall; destruct (dec v g) as [|Hg]; [contradiction|].
        rewrite scoreG_all_gnash_eq_hub, scoreN_all_gnash_eq_rest in Hall.
        destruct (Nat.ltb (hub_weight v + tau v) (rest_weight v)) eqn:Hlt; [discriminate|].
        now apply Nat.ltb_ge in Hlt.
      - intros Hdom s v.
        destruct (dec v g) as [->|Hvg]; [apply next_heaven_tau_at_g|].
        apply domination_tau_implies_glory; [assumption|].
        apply Hdom. assumption.
    Qed.

    Definition need_tau (v:V) : nat := rest_weight v - tau v.
    Definition max_need_tau : nat := list_max (map need_tau nonhubs).

    Lemma max_need_tau_le_iff :
      forall W0, max_need_tau <= W0
        <-> (forall v, v <> g -> rest_weight v - tau v <= W0).
    Proof.
      intro W0; split.
      - intros H v Hvg.
        unfold max_need_tau in H.
        eapply Nat.le_trans; [|exact H].
        unfold need_tau.
        apply list_max_In_le.
        apply (@in_map V nat (fun u => rest_weight u - tau u) nonhubs v).
        apply nonhubs_In_iff; split; [apply allV_complete | exact Hvg].
    - intros H.
      unfold max_need_tau.
      eapply list_max_le_of_forall.
      intros x Hx.
      apply in_map_iff in Hx.
      destruct Hx as [v [Hin Heq]]. 
      rewrite <- Hin; unfold need_tau.
      apply H; apply nonhubs_In_iff in Heq as [_ Hvg]. exact Hvg.
    Qed.

    Lemma le_add_to_sub_le_nat : forall a b t, b <= a + t -> b - t <= a.
    Proof.
      intros a b t H.
      apply (Nat.sub_le_mono_r _ _ t) in H.
      replace (a + t - t) with a in H by lia.
      exact H.
    Qed.

    Lemma sub_le_to_le_add_nat : forall a b t, b - t <= a -> b <= a + t.
    Proof.
      intros a b t H.
      destruct (le_dec t b) as [Htb|Htb].
      - apply (Nat.add_le_mono_r _ _ t) in H.
        assert (Hb : b - t + t = b) by (apply Nat.sub_add; exact Htb).
        rewrite <- Hb. exact H.
      - assert (Hbt : b <= t) by lia.
        assert (Ht : t <= a + t) by (rewrite Nat.add_comm; apply Nat.le_add_r).
        eapply Nat.le_trans; [exact Hbt|exact Ht].
    Qed.
  
    Theorem uniform_hub_tau_one_step_iff :
      (forall s v, next_heaven_tau s v = Glory)
      <-> W >= max_need_tau.
    Proof.
      split.
      - intros Hall.
        apply (proj2 (max_need_tau_le_iff W)).
        intros v Hvg.
        pose proof (proj1 (heaven_one_step_all_G_iff_domination_ge_tau) Hall) as Hdom.
        specialize (Hdom v Hvg).
        rewrite hub_uniform in Hdom by exact Hvg. 
        apply le_add_to_sub_le_nat; exact Hdom.
      - intros HW.
        apply (proj2 (heaven_one_step_all_G_iff_domination_ge_tau)).
        intros v Hvg.
        pose proof (proj1 (max_need_tau_le_iff W) HW) as Hneed.
        specialize (Hneed v Hvg).
        rewrite hub_uniform by exact Hvg.
        apply sub_le_to_le_add_nat; exact Hneed.
    Qed.
  
    Definition need_tau_degmax (v:V) : nat :=
    indeg_nonhub v * max_in_nonhub v - tau v.
    Definition max_need_tau_degmax : nat :=
      list_max (map need_tau_degmax nonhubs).

    Lemma need_tau_le_need_tau_degmax :
      forall v, In v nonhubs -> need_tau v <= need_tau_degmax v.
    Proof.
      intros v Hv.
      unfold need_tau, need_tau_degmax.
      apply Nat.sub_le_mono_r.
      apply rest_le_indeg_times_max.
    Qed.

    Lemma in_map_le_list_max {A} (f : A -> nat) (l : list A) (x : A) :
      In x l -> f x <= list_max (map f l).
    Proof.
      revert x; induction l as [|a l IH]; simpl; intros x H; [contradiction|].
      destruct H as [->|H].
      - apply Nat.le_max_l.
      - specialize (IH _ H).
        eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
    Qed.

    Lemma max_need_tau_le_degmax :
      max_need_tau <= max_need_tau_degmax.
    Proof.
      unfold max_need_tau, max_need_tau_degmax.
      eapply list_max_le_of_forall.
      intros x Hx.
      apply in_map_iff in Hx.
      destruct Hx as [v [Hv Hx]]; subst x.
      transitivity (need_tau_degmax v).
      - apply need_tau_le_need_tau_degmax; assumption.
      - apply in_map_le_list_max; exact Hx.
    Qed.

    Corollary uniform_hub_tau_one_step_sufficient_degmax :
      forall W0, (forall v, v <> g -> hub_weight v = W0) ->
      W0 >= max_need_tau_degmax ->
      (forall s v, next_heaven_tau s v = Glory).
    Proof.
      intros W0 Hunif0 HW0.
      apply (proj2 heaven_one_step_all_G_iff_domination_ge_tau).
      intros v Hvg.
      rewrite Hunif0 by exact Hvg.
      assert (Hneedmax : max_need_tau <= W0)
        by (eapply Nat.le_trans; [apply max_need_tau_le_degmax | exact HW0]).
      pose proof ((proj1 (max_need_tau_le_iff W0) Hneedmax) v Hvg) as Hpt.
      change (rest_weight v <= W0 + tau v).
      rewrite Nat.add_comm.
      eapply sub_le_to_le_add_nat.
      apply le_add_to_sub_le_nat.
      rewrite Nat.add_comm.
      eapply sub_le_to_le_add_nat.
      exact Hpt.
    Qed.

    Hypothesis hub_dominates :  forall v, v <> g -> hub_weight v > rest_weight v.
    Hypothesis hub_dominates_ge : forall v, v <> g -> hub_weight v >= rest_weight v.
    
    Theorem heaven_one_step_all_G :
      forall s v, next_heaven s v = Glory.
    Proof.
      intros s v.
      unfold next_heaven.
      destruct (dec v g) as [->|Hvg]; [reflexivity|].
      set (s' := force_g s).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash  v).
      assert (HNle : SN <= rest_weight v) by (subst SN s'; apply scoreN_le_rest).
      assert (Hrest : rest_weight v <= hub_weight v) by (apply hub_dominates_ge; exact Hvg).
      assert (Hhub  : hub_weight v <= SG) by (subst SG s'; apply scoreG_ge_hub).
      assert (Hle : SN <= SG).
      { eapply Nat.le_trans; [apply HNle|].
        eapply Nat.le_trans; [apply Hrest|apply Hhub]. }
      assert (Hltb : SG <? SN = false).
      { apply (proj2 (Nat.ltb_ge SG SN)). exact Hle. }
      rewrite Hltb. reflexivity.
    Qed.

    Definition all_glory : statef := fun _ => Glory.
    Lemma all_glory_fixed :
      forall v, next_heaven all_glory v = Glory.
    Proof. apply heaven_one_step_all_G. Qed.

  Definition async_update (s:statef) (v:V) : statef :=
      fun u => if dec u v then next_heaven s v else s u.
  Definition run_sched (s:statef) (sched:list V) : statef :=
      fold_left async_update sched s.
 
    Lemma async_update_at :
      forall s v, async_update s v v = next_heaven s v.
    Proof. intros s v. unfold async_update. destruct (dec v v); [reflexivity|contradiction]. Qed.
    
    Lemma async_update_other :
      forall s v u, u <> v -> async_update s v u = s u.
    Proof.
      intros s v u Huv. unfold async_update.
      destruct (dec u v) as [E|]; [congruence|reflexivity].
    Qed.

    Lemma unchanged_if_not_in :
      forall sched s v, ~ In v sched -> run_sched s sched v = s v.
    Proof.
      induction sched as [|a tl IH]; intros s v Hnin.
      - cbn. reflexivity.
      - cbn [run_sched fold_left].
        assert (Hneq : v <> a) by (intro E; apply Hnin; left; symmetry; exact E).
        assert (Hnintl : ~ In v tl) by (intro Hin; apply Hnin; right; exact Hin).
        change (fold_left async_update tl (async_update s a) v) with (run_sched (async_update s a) tl v).
        rewrite IH by exact Hnintl.
        now rewrite async_update_other by exact Hneq.
    Qed.
    
    Lemma in_sched_makes_Glory :
      forall sched s v, In v sched -> run_sched s sched v = Glory.
    Proof.
      induction sched as [|a tl IH]; intros s v Hin.
      - contradiction.
      - cbn [run_sched fold_left].
        destruct Hin as [Hv | Hin_tl].
        + set (s' := async_update s a).
          assert (Hseta : s' a = Glory).
          { subst s'. rewrite async_update_at. apply heaven_one_step_all_G. }
          change (fold_left async_update tl s' v) with (run_sched s' tl v).
          destruct (in_dec dec v tl) as [Hin' | Hnin'].
          * apply IH; exact Hin'.
          * rewrite (unchanged_if_not_in tl s' v Hnin').
            rewrite <- Hv. exact Hseta.
        + change (fold_left async_update tl (async_update s a) v)
            with (run_sched (async_update s a) tl v).
          apply IH; exact Hin_tl.
    Qed.
    
    Theorem async_one_pass_all_G_nonhub :
      forall sched s,
        (forall v, v <> g -> In v sched) ->
        forall v, v <> g -> run_sched s sched v = Glory.
    Proof.
      intros sched s Hcover v Hv.
      apply in_sched_makes_Glory; apply Hcover; exact Hv.
    Qed.

    Theorem async_one_pass_all_G_all :
      forall sched s,
        (forall v, In v sched) ->
        forall v, run_sched s sched v = Glory.
    Proof.
      intros sched s Hcover v.
      apply in_sched_makes_Glory; apply Hcover.
    Qed.
    
    Definition set := V -> bool.
    Definition seed_state (S:set) (s:statef) : statef := fun u => if S u then Glory else s u.
    Definition w_from (S:set) (v:V) : nat := sum_all (fun u => if dec u g then 0 else if S u then w u v else 0).
    Definition rest_outside (S:set) (v:V) : nat := sum_all (fun u => if dec u g then 0 else if S u then 0 else w u v).
    
    Lemma rest_split_by_S :
      forall S v, rest_weight v = w_from S v + rest_outside S v.
    Proof.
      intros S v. unfold rest_weight, w_from, rest_outside.
      rewrite <- (sum_all_add
        (fun u => if dec u g then 0 else if S u then w u v else 0)
        (fun u => if dec u g then 0 else if S u then 0      else w u v)).
      apply sum_all_ext; intros u _; destruct (dec u g); destruct (S u); lia.
    Qed.
    
    Lemma mul_ind_nonneg n b : 0 <= n * ind b.
    Proof. destruct b; cbn [ind]; lia. Qed.
    
    Lemma le_mul_ind_true n : n <= n * ind true.
    Proof. cbn [ind]; lia. Qed.

    Lemma scoreG_seed_lower :
      forall S s v,
        hub_weight v + w_from S v
        <= score (force_g (seed_state S s)) Glory v.
    Proof.
      intros S s v.
      rewrite (scoreG_split (seed_state S s) v).
      unfold w_from.
      apply Nat.add_le_mono_l.
      eapply sum_all_le; intros u _.
      destruct (dec u g) as [->|Hug]; cbn; [lia|].
      destruct (S u) eqn:Su.
      - unfold seed_state; rewrite Su; cbn [state_eqb ind].
        apply le_mul_ind_true.
      - unfold seed_state; rewrite Su; cbn [state_eqb ind].
        apply mul_ind_nonneg.
    Qed.
    
    Lemma scoreN_seed_upper :
      forall S s v,
        score (force_g (seed_state S s)) Gnash v
        <= rest_outside S v.
    Proof.
      intros S s v.
      unfold rest_outside, score, seed_state, force_g.
      eapply sum_all_le; intros u _.
      destruct (dec u g) as [|Hug]; cbn; [lia|].
      destruct (S u) eqn:Su; cbn.
      - lia.
      - apply mul_ind_le.
    Qed.
    
    Lemma two_step_sufficient :
      forall S s v, v <> g ->
        hub_weight v + w_from S v >= rest_outside S v ->
        next_heaven (seed_state S s) v = Glory.
    Proof.
      intros S s v Hvg Hdom.
      unfold next_heaven.
      destruct (dec v g) as [|Hg]; [contradiction|].
      set (s' := force_g (seed_state S s)).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash v).
      pose proof (scoreG_seed_lower S s v)  as Hge;  cbv zeta in Hge.
      pose proof (scoreN_seed_upper S s v)  as Hle;  cbv zeta in Hle.
      assert (SN <= SG).
      { eapply Nat.le_trans; [apply Hle|].
        eapply Nat.le_trans; [apply Hdom|].
        exact Hge. }
      apply (proj2 (Nat.ltb_ge SG SN)) in H; rewrite H; reflexivity.
    Qed.

    Lemma two_step_sufficient_tau :
      forall (S:set) s v,
        v <> g ->
        hub_weight v + w_from S v + tau v >= rest_outside S v ->
        next_heaven_tau (seed_state S s) v = Glory.
    Proof.
      intros S s v Hvg Hdom.
      unfold next_heaven_tau.
      destruct (dec v g) as [|Hg]; [contradiction|].
      set (s' := force_g (seed_state S s)).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash  v).
      pose proof (scoreG_seed_lower S s v)  as Hge;  cbv zeta in Hge.
      pose proof (scoreN_seed_upper S s v)  as Hle;  cbv zeta in Hle.
      assert (H1 : SN <= rest_outside S v) by exact Hle.
      assert (H2 : rest_outside S v <= hub_weight v + w_from S v + tau v) by exact Hdom.
      assert (H3 : hub_weight v + w_from S v + tau v <= SG + tau v).
      { apply Nat.add_le_mono_r. exact Hge. }
      assert (Hle' : SN <= SG + tau v).
      { eapply Nat.le_trans; [eapply Nat.le_trans; [exact H1|exact H2]|exact H3]. }
      destruct (Nat.ltb (SG + tau v) SN) eqn:Hlt;
        [apply Nat.ltb_lt in Hlt; lia | reflexivity].
    Qed.

    Definition is_heavenly (S:set) : Prop :=
      forall v, v <> g -> S v = true ->
        rest_outside S v <= hub_weight v + w_from S v + tau v.

    Theorem heavenly_seed_one_step :
      forall (S:set) s v,
        is_heavenly S ->
        v <> g ->
        S v = true ->
        next_heaven_tau (seed_state S s) v = Glory.
    Proof.
      intros S s v Hhev Hvg Hv.
      apply two_step_sufficient_tau; [assumption|].
      exact (Hhev v Hvg Hv).
    Qed.

    Corollary heavenly_everyone_one_step :
      forall (S:set) s,
        is_heavenly S ->
        (forall v, v <> g -> S v = true) ->
        forall v, v <> g -> next_heaven_tau (seed_state S s) v = Glory.
    Proof.
      intros S s Hhev Hall v Hvg.
      apply heavenly_seed_one_step; auto.
    Qed.

    Lemma all_glory_tau_fixed :
      forall v, next_heaven_tau all_glory v = Glory.
    Proof.
      intros v.
      unfold next_heaven_tau.
      destruct (dec v g) as [->|Hvg]; [reflexivity|].
      set (s' := force_g all_glory).
      set (SG := score s' Glory v).
      set (SN := score s' Gnash  v).

      (* Under [all_glory], nobody gnashes, so SN = 0 *)
      assert (SN0 : SN = 0).
      { unfold SN, score, s', force_g, all_glory, sum_all.
        rewrite (@map_ext_in V nat
                  (fun u => w u v *
                            ind (state_eqb (if dec u g then Glory else Glory) Gnash))
                  (fun _ => 0) allV).
        - apply (@fold_sum_map_zero V allV).
        - intros u _. destruct (dec u g); cbn [state_eqb ind]. all: rewrite Nat.mul_0_r; reflexivity.
      }
      rewrite SN0.
      destruct (Nat.ltb (SG + tau v) 0) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|].
      reflexivity.
    Qed.

    Definition S_nonhub : set := fun u => if dec u g then false else true.
    
    Lemma w_from_all_nonhub_eq_rest :
      forall v, w_from S_nonhub v = rest_weight v.
    Proof.
      intro v.
      unfold w_from, rest_weight, S_nonhub.
      apply sum_all_ext; intros u _.
      destruct (dec u g); cbn; reflexivity.
    Qed.
    

    Lemma rest_outside_all_nonhub_eq_0 :
      forall v, rest_outside S_nonhub v = 0.
    Proof.
      intro v.
      unfold rest_outside, S_nonhub.
      assert (Hsum :
        sum_all
          (fun u =>
             if dec u g then 0
             else if (if dec u g then false else true) then 0 else w u v)
        = sum_all (fun _ => 0)).
      { apply sum_all_ext. intros u _.
        destruct (dec u g); cbn; reflexivity. }
      rewrite Hsum.
      unfold sum_all.
      rewrite (@fold_sum_map_zero V allV).
      reflexivity.
    Qed.
    
    Lemma omnipresent_seed_next_is_Glory :
      forall s v, v <> g -> next_heaven (seed_state S_nonhub s) v = Glory.
    Proof.
      intros s v Hvg.
      apply two_step_sufficient with (S:=S_nonhub); try assumption.
      rewrite rest_outside_all_nonhub_eq_0.
      lia.
    Qed.
  End Generic.

  Module HellC4.

    Inductive V4 := v1 | v2 | v3 | v4.
    Definition decV4 (x y:V4) : {x=y}+{x<>y}.
    Proof. decide equality. Qed.
    
    Definition allV4 := [v1;v2;v3;v4].
    Lemma nodup_allV4 : NoDup allV4. 
    Proof.
      repeat constructor.
      - cbn; intros [H|[H|[H|[]]]]; discriminate.
      - cbn; intros [H|[H|[]]]; discriminate.
      - cbn; intros [H|[]]; discriminate.
      - cbn; intros [].
    Qed.
    
    Lemma complete_allV4 : forall v:V4, In v allV4.
    Proof. intro v; destruct v; cbn; tauto. Qed.
    
    Definition w4 (u v:V4) : nat :=
      match u, v with
      | v1, v2 | v1, v4
      | v2, v1 | v2, v3
      | v3, v2 | v3, v4
      | v4, v3 | v4, v1 => 1
      | _, _ => 0
      end.
    Definition score4 : (V4 -> State) -> State -> V4 -> nat :=
      @score V4 allV4 w4.
    Definition next_hell (s:V4->State) (v:V4) : State :=
      let SG := score4 s Glory v in
      let SN := score4 s Gnash v in
      if Nat.ltb SG SN then Gnash else Glory.
    (* Checkerboard initial configuration: G,N,G,N *)
    Definition s0 (v:V4) : State :=
      match v with v1 => Glory | v2 => Gnash | v3 => Glory | v4 => Gnash end.
    (* Its flip after one synchronous step: N,G,N,G *)
    Definition s1 (v:V4) : State :=
      match v with v1 => Gnash | v2 => Glory | v3 => Gnash | v4 => Glory end.

    Lemma hell_flip_once :
      forall v, next_hell s0 v = s1 v.
    Proof.
      intro v. destruct v; cbn.
      all: reflexivity. 
    Qed.
    
    Lemma score4_ext :
      forall (s t : V4 -> State) (x : State) (v : V4),
        (forall u, s u = t u) ->
        score4 s x v = score4 t x v.
    Proof.
      intros s t x v Heq.
      unfold score4, score.
      eapply (@sum_all_ext V4 allV4). 
      intros u _; now rewrite Heq.
    Qed.

    Lemma next_hell_ext :
      forall (s t : V4 -> State),
        (forall u, s u = t u) ->
        forall v, next_hell s v = next_hell t v.
    Proof.
      intros s t Heq v.
      unfold next_hell.
      rewrite (score4_ext s t Glory v Heq),
              (score4_ext s t Gnash v Heq).
      reflexivity.
    Qed.

    Lemma hell_flip_once_back :
      forall v, next_hell s1 v = s0 v.
    Proof. intro v; destruct v; cbn; reflexivity. Qed.

    Lemma hell_two_cycle :
      forall v, next_hell (fun x => next_hell s0 x) v = s0 v.
    Proof.
      intro v.
      replace (next_hell (fun x => next_hell s0 x) v) with (next_hell s1 v).
      - apply hell_flip_once_back.
      - symmetry.
        apply next_hell_ext. intro u.
        apply hell_flip_once.
    Qed.
  End HellC4.

  Module HeavenExample.

    Inductive HV := h | v1 | v2 | v3 | v4.
    Definition decHV (x y:HV) : {x=y}+{x<>y}. Proof. decide equality. Qed.
    Definition allHV := [h; v1; v2; v3; v4].

    Lemma nodup_allHV : NoDup allHV.
    Proof.
      repeat constructor.
      - cbn; intros [H|[H|[H|[H|[]]]]]; discriminate.
      - cbn; intros [H|[H|[H|[]]]]; discriminate.
      - cbn; intros [H|[H|[]]]; discriminate.
      - cbn; intros [H|[]]; discriminate.
      - cbn; intros [].
    Qed.

    Lemma complete_allHV : forall v:HV, In v allHV.
    Proof. intro v; destruct v; cbn; tauto. Qed.

    (* Hub-to-everyone weight W must dominate (strictly exceed 2). *)
    Local Parameter W : nat.
    Local Parameter W_ge_2 : 2 <= W.
    Local Parameter W_gt_2 : 2 < W.


    (* Base 4-cycle (unit weights), no edges touching h. *)
    Definition wC (u v:HV) : nat :=
      match u, v with
      | v1, v2 | v1, v4
      | v2, v1 | v2, v3
      | v3, v2 | v3, v4
      | v4, v3 | v4, v1 => 1
      | _, _ => 0
      end.

    (* Hub contributes W into each vi; nothing else. *)
    Definition wHub (u v:HV) : nat :=
      match u, v with
      | h, v1 | h, v2 | h, v3 | h, v4 => W
      | _, _ => 0
      end.

    (* Total influence: cycle + hub. *)
    Definition w5 (u v:HV) : nat := wC u v + wHub u v.
    Definition hub_weight5 (v:HV) : nat :=
      @hub_weight HV w5 h v. 
    Definition rest_weight5 (v:HV) : nat :=
      @rest_weight HV decHV allHV w5 h v.
    Definition next_heaven5 (s:HV->State) (v:HV) : State :=
      @next_heaven HV decHV allHV w5 h s v.

    (* Compute hub weights. *)
    Lemma hub_weight5_v1 : hub_weight5 v1 = W. Proof. reflexivity. Qed.
    Lemma hub_weight5_v2 : hub_weight5 v2 = W. Proof. reflexivity. Qed.
    Lemma hub_weight5_v3 : hub_weight5 v3 = W. Proof. reflexivity. Qed.
    Lemma hub_weight5_v4 : hub_weight5 v4 = W. Proof. reflexivity. Qed.
    Lemma hub_weight5_h  : hub_weight5 h  = 0. Proof. reflexivity. Qed.

    (* Total incoming weight at each node. *)
    Lemma total_in_v1 :
      @sum_all HV allHV (fun u => w5 u v1) = W + 2.
    Proof. cbn; lia. Qed.
    Lemma total_in_v2 :
      @sum_all HV allHV (fun u => w5 u v2) = W + 2.
    Proof. cbn; lia. Qed.
    Lemma total_in_v3 :
      @sum_all HV allHV (fun u => w5 u v3) = W + 2.
    Proof. cbn; lia. Qed.
    Lemma total_in_v4 :
      @sum_all HV allHV (fun u => w5 u v4) = W + 2.
    Proof. cbn; lia. Qed.
    Lemma total_in_h :
      @sum_all HV allHV (fun u => w5 u h) = 0.
    Proof. cbn; lia. Qed.

    (* Generic decomposition: total = hub + rest. *)
    Lemma total_split5 :
      forall v, @sum_all HV allHV (fun u => w5 u v)
                = hub_weight5 v + rest_weight5 v.
    Proof.
      intro v.
      exact (@total_weight_split HV decHV allHV nodup_allHV complete_allHV w5 h v).
    Qed.

    (* Therefore the non-hub rest into each vi is exactly 2. *)
    Lemma rest_is_two_v1 : rest_weight5 v1 = 2.
    Proof. pose proof (total_split5 v1) as H; rewrite total_in_v1, hub_weight5_v1 in H; lia. Qed.
    Lemma rest_is_two_v2 : rest_weight5 v2 = 2.
    Proof. pose proof (total_split5 v2) as H; rewrite total_in_v2, hub_weight5_v2 in H; lia. Qed.
    Lemma rest_is_two_v3 : rest_weight5 v3 = 2.
    Proof. pose proof (total_split5 v3) as H; rewrite total_in_v3, hub_weight5_v3 in H; lia. Qed.
    Lemma rest_is_two_v4 : rest_weight5 v4 = 2.
    Proof. pose proof (total_split5 v4) as H; rewrite total_in_v4, hub_weight5_v4 in H; lia. Qed.

    Definition all_gnash5 : HV -> State := fun _ => Gnash.
    
    Lemma scoreG_all_gnash_is_hub :
      forall v,
        @score HV allHV w5
          (@force_g HV decHV h all_gnash5) Glory v
        = hub_weight5 v.
    Proof.
      intro v.
      pose proof (@scoreG_split
                    HV decHV allHV nodup_allHV complete_allHV
                    w5 h all_gnash5 v) as Hsplit.
      rewrite Hsplit.
      unfold hub_weight5.
      assert (H0 :
        sum_all allHV (fun u =>
          if decHV u h then 0
          else w5 u v * ind (state_eqb (all_gnash5 u) Glory)) = 0).
      { assert (Hzero :
          sum_all allHV (fun u : HV =>
            if decHV u h then 0 else w5 u v * ind (state_eqb (all_gnash5 u) Glory))
          =
          sum_all allHV (fun _ => 0)).
        { eapply (@sum_all_ext HV allHV).
          intros u _; destruct (decHV u h); cbn; [reflexivity|].
          now rewrite Nat.mul_0_r.
        }
        rewrite Hzero. unfold sum_all; cbn; lia.
      }
      rewrite H0. now rewrite Nat.add_0_r.
    Qed.
    
    Lemma scoreN_all_gnash_is_rest :
      forall v,
        @score HV allHV w5
          (@force_g HV decHV h all_gnash5) Gnash v
        = rest_weight5 v.
    Proof.
      intro v.
      unfold rest_weight5, score, all_gnash5, force_g.
      eapply (@sum_all_ext HV allHV).
      intros u _.
      destruct (decHV u h); cbn; lia.
    Qed.

    Lemma W_le_1_counterexample :
      W <= 1 -> next_heaven5 all_gnash5 v1 = Gnash.
    Proof.
      intro Hle.
      unfold next_heaven5, next_heaven.
      destruct (decHV v1 h) as [E|_]; [discriminate|].
      rewrite (scoreG_all_gnash_is_hub v1),
              (scoreN_all_gnash_is_rest v1),
              hub_weight5_v1, rest_is_two_v1.
      assert (Hlt : W < 2) by lia.
      apply (proj2 (Nat.ltb_lt W 2)) in Hlt.
      rewrite Hlt.
      reflexivity.
    Qed.
    
    Lemma W_le_1_counterexample_all :
      W <= 1 -> forall v, v <> h -> next_heaven5 all_gnash5 v = Gnash.
    Proof.
      intros Hle v Hv.
      unfold next_heaven5, next_heaven.
      destruct (decHV v h) as [E|E]; [congruence|].
      rewrite (scoreG_all_gnash_is_hub v),
              (scoreN_all_gnash_is_rest v).
      assert (HW2 : (W <? 2) = true).
      { apply (proj2 (Nat.ltb_lt W 2)). lia. }
      destruct v; try contradiction.
      - rewrite hub_weight5_v1, rest_is_two_v1, HW2. reflexivity.
      - rewrite hub_weight5_v2, rest_is_two_v2, HW2. reflexivity.
      - rewrite hub_weight5_v3, rest_is_two_v3, HW2. reflexivity.
      - rewrite hub_weight5_v4, rest_is_two_v4, HW2. reflexivity.
    Qed.

    (* Dominance condition needed by the generic theorem. *)
    Lemma hub_dominates_ge_5 :
      forall v, v <> h -> hub_weight5 v >= rest_weight5 v.
    Proof.
      intros v Hneq; destruct v; try contradiction;
        rewrite ?hub_weight5_v1, ?hub_weight5_v2, ?hub_weight5_v3, ?hub_weight5_v4;
        rewrite ?rest_is_two_v1, ?rest_is_two_v2, ?rest_is_two_v3, ?rest_is_two_v4;
        exact W_ge_2.
    Qed.

    Lemma hub_dominates_5 :
      forall v, v <> h -> hub_weight5 v > rest_weight5 v.
    Proof.
      intros v Hneq; destruct v; try contradiction;
        rewrite ?hub_weight5_v1, ?hub_weight5_v2, ?hub_weight5_v3, ?hub_weight5_v4;
        rewrite ?rest_is_two_v1, ?rest_is_two_v2, ?rest_is_two_v3, ?rest_is_two_v4;
        exact W_gt_2.
    Qed.

    Theorem heaven5_one_step_all_G :
      forall s v, next_heaven5 s v = Glory.
    Proof.
      intros s v.
      unfold next_heaven5.
      eapply heaven_one_step_all_G.
      - exact complete_allHV.
      - exact hub_dominates_ge_5. 
    Qed.

  End HeavenExample.

End HeavenHell.
