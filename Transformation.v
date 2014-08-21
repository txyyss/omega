Require Import Theory.
Require Import ZArith.
Require Import String Ascii.
Require Import Bool.
Require Import NPeano.
Require Import FunctionalExtensionality.
Open Scope string_scope.

Import ZInfinity.

(* String Variable Type for Extraction  *)
Module Type STRVAR <: VARIABLE.
  Parameter var : Type. (* who konws what it is, but in reality it's OCaml string *)
  Parameter var_eq_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
  Parameter var2string : var -> string.
  Parameter string2var : string -> var.
  Axiom var2String2var : forall v, string2var(var2string v) = v.
  Axiom String2var2String : forall s, var2string(string2var s) = s.
End STRVAR.

Module InfSolver (sv:STRVAR) (VAL : SEM_VAL) (S: NONE_RELATION VAL).
  Import sv.
  Import VAL.
  Import S.

  Module InfRel := InfLeqRelation VAL S.
  Module FinRel := FinLeqRelation VAL.

  (* Both variable and constant domain can be integers with infinity. *)
  Module IA := ArithSemantics PureInfinity sv VAL S InfRel.

  (* Both variable and constant domain are integers. *)
  Module FA := ArithSemantics PureInt sv VAL S FinRel.

  (* Variable domain is integers and constant domain is integers with infinity. *)
  Module I2F := ArithSemantics IntToInfinity sv VAL S InfRel.

  (* Transform expressions in IA to I2F *)
  Fixpoint inf_trans_exp (exp : IA.ZExp) : I2F.ZExp :=
    match exp with
        IA.ZExp_Var v => I2F.ZExp_Var v
      | IA.ZExp_Const a => I2F.ZExp_Const a
      | IA.ZExp_Add e1 e2 => I2F.ZExp_Add (inf_trans_exp e1) (inf_trans_exp e2)
      | IA.ZExp_Inv e => I2F.ZExp_Inv (inf_trans_exp e)
      | IA.ZExp_Sub e1 e2 => I2F.ZExp_Sub (inf_trans_exp e1) (inf_trans_exp e2)
      | IA.ZExp_Mult z e => I2F.ZExp_Mult z (inf_trans_exp e)
    end.

  (* Expression transformation keeps the evaluation. *)
  Lemma inf_trans_exp_ok : forall exp, IA.dexp2ZE exp = I2F.dexp2ZE (inf_trans_exp exp).
  Proof.
    induction exp; simpl; auto;
    try (rewrite IHexp1, IHexp2; auto);
    try (rewrite IHexp; auto).
  Qed.

  (* Transform boolean forms in IA to I2F *)
  Definition inf_trans_bf (bf : IA.ZBF) : I2F.ZBF :=
    match bf with
        IA.ZBF_Const b => I2F.ZBF_Const b
      | IA.ZBF_Lt f1 f2 => I2F.ZBF_Lt (inf_trans_exp f1) (inf_trans_exp f2)
      | IA.ZBF_Lte f1 f2 => I2F.ZBF_Lte (inf_trans_exp f1) (inf_trans_exp f2)
      | IA.ZBF_Gt f1 f2 => I2F.ZBF_Gt (inf_trans_exp f1) (inf_trans_exp f2)
      | IA.ZBF_Gte f1 f2 => I2F.ZBF_Gte (inf_trans_exp f1) (inf_trans_exp f2)
      | IA.ZBF_Eq f1 f2 => I2F.ZBF_Eq (inf_trans_exp f1) (inf_trans_exp f2)
      | IA.ZBF_Eq_Max f1 f2 f3 => I2F.ZBF_Eq_Max (inf_trans_exp f1) (inf_trans_exp f2) (inf_trans_exp f3)
      | IA.ZBF_Eq_Min f1 f2 f3 => I2F.ZBF_Eq_Min (inf_trans_exp f1) (inf_trans_exp f2) (inf_trans_exp f3)
      | IA.ZBF_Neq f1 f2 => I2F.ZBF_Neq (inf_trans_exp f1) (inf_trans_exp f2)
    end.

  (* Boolean form transformation keeps the validity. *)
  Lemma inf_trans_bf_ok : forall z, IA.satisfied (IA.ZF_BF z) <-> I2F.satisfied (I2F.ZF_BF (inf_trans_bf z)).
  Proof.
    destruct z; simpl;
    rewrite IA.satisfied_unfold, I2F.satisfied_unfold;
    simpl; repeat rewrite inf_trans_exp_ok; tauto.
  Qed.

  Lemma inf_trans_bf_dst : forall z, IA.dissatisfied (IA.ZF_BF z) <-> I2F.dissatisfied (I2F.ZF_BF (inf_trans_bf z)).
  Proof.
    destruct z; simpl;
    rewrite IA.dissatisfied_unfold, I2F.dissatisfied_unfold;
    simpl; repeat rewrite inf_trans_exp_ok; tauto.
  Qed.

  (* Transform logic forms in IA to I2F *)
  Definition inf_trans : IA.ZF -> I2F.ZF :=
    Fix IA.lengthOrder_wf (fun _ => I2F.ZF)
        (fun (form : IA.ZF) =>
           match form return ((forall f : IA.ZF, IA.lengthOrder f form -> I2F.ZF) -> I2F.ZF) with
               IA.ZF_BF bf => fun _ => I2F.ZF_BF (inf_trans_bf bf)
             | IA.ZF_And f1 f2 => fun infTrans => I2F.ZF_And (infTrans f1 (IA.lengthOrder_and_1 f1 f2))
                                                             (infTrans f2 (IA.lengthOrder_and_2 f1 f2))
             | IA.ZF_Or f1 f2 => fun infTrans => I2F.ZF_Or (infTrans f1 (IA.lengthOrder_or_1 f1 f2))
                                                           (infTrans f2 (IA.lengthOrder_or_2 f1 f2))
             | IA.ZF_Imp f1 f2 => fun infTrans => I2F.ZF_Imp (infTrans f1 (IA.lengthOrder_imp_1 f1 f2))
                                                             (infTrans f2 (IA.lengthOrder_imp_2 f1 f2))
             | IA.ZF_Not f' => fun infTrans => I2F.ZF_Not (infTrans f' (IA.lengthOrder_not f'))
             | IA.ZF_Forall v q f' =>
               match q with
                   PureInfinity.Q_Z =>
                   fun infTrans => I2F.ZF_Forall v tt (infTrans f' (IA.lengthOrder_forall_trivial f' v PureInfinity.Q_Z))
                 | PureInfinity.Q_ZE =>
                   fun infTrans =>
                     I2F.ZF_And (I2F.ZF_Forall v tt (infTrans f' (IA.lengthOrder_forall_trivial f' v PureInfinity.Q_ZE)))
                                (I2F.ZF_And (infTrans (IA.substitute (v, Some ZE_Inf) f')
                                                      (IA.lengthOrder_forall f' v PureInfinity.Q_ZE ZE_Inf))
                                            (infTrans (IA.substitute (v, Some ZE_NegInf) f')
                                                      (IA.lengthOrder_forall f' v PureInfinity.Q_ZE ZE_NegInf)))
               end
             | IA.ZF_Exists v q f' =>
               match q with
                   PureInfinity.Q_Z =>
                   fun infTrans => I2F.ZF_Exists v tt (infTrans f' (IA.lengthOrder_exists_trivial f' v PureInfinity.Q_Z))
                 | PureInfinity.Q_ZE =>
                   fun infTrans =>
                     I2F.ZF_Or (I2F.ZF_Exists v tt (infTrans f' (IA.lengthOrder_exists_trivial f' v PureInfinity.Q_ZE)))
                               (I2F.ZF_Or (infTrans (IA.substitute (v, Some ZE_Inf) f')
                                                    (IA.lengthOrder_exists f' v PureInfinity.Q_ZE ZE_Inf))
                                          (infTrans (IA.substitute (v, Some ZE_NegInf) f')
                                                    (IA.lengthOrder_exists f' v PureInfinity.Q_ZE ZE_NegInf)))
               end
           end).

  Lemma inf_trans_unfold: forall form,
                            inf_trans form =
                            match form with
                                IA.ZF_BF bf => I2F.ZF_BF (inf_trans_bf bf)
                              | IA.ZF_And f1 f2 => I2F.ZF_And (inf_trans f1) (inf_trans f2)
                              | IA.ZF_Or f1 f2 => I2F.ZF_Or (inf_trans f1) (inf_trans f2)
                              | IA.ZF_Imp f1 f2 => I2F.ZF_Imp (inf_trans f1) (inf_trans f2)
                              | IA.ZF_Not f => I2F.ZF_Not (inf_trans f)
                              | IA.ZF_Forall v q f =>
                                match q with
                                    PureInfinity.Q_Z => I2F.ZF_Forall v tt (inf_trans f)
                                  | PureInfinity.Q_ZE => I2F.ZF_And (I2F.ZF_Forall v tt (inf_trans f))
                                                                    (I2F.ZF_And (inf_trans (IA.substitute (v, Some ZE_Inf) f))
                                                                                (inf_trans (IA.substitute (v, Some ZE_NegInf) f)))
                                end
                              | IA.ZF_Exists v q f =>
                                match q with
                                    PureInfinity.Q_Z => I2F.ZF_Exists v tt (inf_trans f)
                                  | PureInfinity.Q_ZE => I2F.ZF_Or (I2F.ZF_Exists v tt (inf_trans f))
                                                                   (I2F.ZF_Or (inf_trans (IA.substitute (v, Some ZE_Inf) f))
                                                                              (inf_trans (IA.substitute (v, Some ZE_NegInf) f)))
                                end
                            end.
  Proof.
    intro; unfold inf_trans at 1; rewrite Fix_eq.
    destruct form; auto;
    destruct q; auto.
    intros; match goal with
              | [H : forall (y : IA.ZF) (p : IA.lengthOrder y ?x), ?f y p = ?g y p |- _ ] =>
                assert (HFunEq: f = g) by (extensionality as1; extensionality as2; auto);
                  destruct x; auto; repeat (f_equal; auto); rewrite HFunEq; reflexivity
            end.
  Qed.

  (* Substitution and expression transformation from IA to I2F are commutative. *)
  Lemma subst_inf_trans_exp_eq : forall z v (x : option ZE),
                                   I2F.subst_exp (v, x) (inf_trans_exp z) = inf_trans_exp (IA.subst_exp (v, x) z).
  Proof.
    induction z; simpl; intros;
    try (destruct (var_eq_dec v0 v); simpl);
    try (rewrite IHz1, IHz2);
    try (rewrite IHz);
    auto.
  Qed.

  (* Substitution and boolean form transformation from IA to I2F are commutative. *)
  Lemma subst_inf_trans_bf_eq : forall z v (x : option ZE),
                                  I2F.substitute (v, x) (inf_trans (IA.ZF_BF z)) =
                                  inf_trans (IA.substitute (v, x) (IA.ZF_BF z)).
  Proof.
    destruct z; simpl; intros;
    unfold inf_trans;
    unfold IA.length_zform;
    simpl; auto;
    repeat rewrite subst_inf_trans_exp_eq; auto.
  Qed.

  Ltac unfold_right_inf_trans :=
    match goal with
      | [|- _ = inf_trans ?X] => rewrite inf_trans_unfold with X; auto
    end.

  (* Substitution and logic form transformation from IA to I2F are commutative. *)
  Lemma subst_inf_trans_eq: forall f v (x: option ZE), I2F.substitute (v, x) (inf_trans f) = inf_trans (IA.substitute (v, x) f).
  Proof.
    intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H;
    induction n; intros;
    [ destruct f; exfalso; simpl in H; intuition |
      destruct f; simpl in H; apply le_S_n in H;
      let solve_cnt := (rewrite inf_trans_unfold; simpl; rewrite (IHn f1), (IHn f2);
                        [unfold_right_inf_trans | omega | omega ]) in
      let solve_quant :=
          rewrite inf_trans_unfold; destruct q; simpl;
          [destruct (var_eq_dec v v0); unfold_right_inf_trans; rewrite IHn; auto |
           destruct (var_eq_dec v v0); repeat rewrite <- IHn; auto;
           [rewrite e; repeat rewrite I2F.same_var_subst |
            repeat rewrite I2F.diff_var_subst with (v1 := v) (v2 := v0); auto];
           unfold_right_inf_trans; repeat rewrite IHn; auto; rewrite <- IA.substitute_length_inv; auto] in
      solve [rewrite subst_inf_trans_bf_eq; auto | solve_cnt | solve_cnt | solve_cnt |
             rewrite inf_trans_unfold; simpl; rewrite IHn; [unfold_right_inf_trans | omega ] |
             solve_quant | solve_quant]].
  Qed.

  Ltac solve_le_inv :=
    match goal with
      | [|- IA.length_zform (IA.substitute _ _) <= _] => rewrite <- IA.substitute_length_inv; auto
    end.

  (* Logic form transformation from IA to I2F keeps the validity. *)
  Lemma inf_trans_ok : forall f, (IA.satisfied f <-> I2F.satisfied (inf_trans f)) /\
                                 (IA.dissatisfied f <-> I2F.dissatisfied (inf_trans f)).
  Proof.
    intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H.
    induction n; intros.
    exfalso; destruct f; simpl in H; intuition.
    split.
    (* ok part *)
    destruct f; simpl in H; apply le_S_n in H; rewrite inf_trans_unfold; try (rewrite inf_trans_bf_ok; intuition);
    rewrite IA.satisfied_unfold, I2F.satisfied_unfold.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S: IA.length_zform f <= n) by omega; destruct (IHn _ S); intuition.

    assert (INV1: IA.length_zform (IA.substitute (v,Some ZE_Inf) f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
    assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf) f)<= n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
    destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
    split; intros; assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST];
    [rewrite subst_inf_trans_eq; rewrite <- SAT | rewrite SAT; rewrite <- subst_inf_trans_eq]; apply H0.
    do 2 rewrite I2F.satisfied_unfold; split; intros.
    split; intros.
    assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST].
    rewrite subst_inf_trans_eq; rewrite <- SAT; apply H0.
    split; [rewrite <- SAT1 | rewrite <- SAT2].
    apply H0. apply H0. destruct H0 as [? [? ?]].
    destruct x.
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite SAT; rewrite <- subst_inf_trans_eq; apply H0.
    rewrite SAT1; apply H1. rewrite SAT2; apply H2.

    assert (INV1: IA.length_zform (IA.substitute (v,Some ZE_Inf) f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
    assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf) f)<= n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
    destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
    split; intros; destruct H0 as [x H0]; exists x;
    assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST];
    [rewrite subst_inf_trans_eq; rewrite <- SAT | rewrite SAT; rewrite <- subst_inf_trans_eq]; apply H0.
    do 2 rewrite I2F.satisfied_unfold; split; intros.
    destruct H0 as [x H0]; destruct x.
    left; exists z; rewrite subst_inf_trans_eq.
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite <- SAT; apply H0.
    right; left; rewrite <- SAT1; apply H0.
    right; right; rewrite <- SAT2; apply H0.
    destruct H0; destruct H0.
    exists (ZE_Fin x).
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_ZE (ZE_Fin x)) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite SAT; rewrite <- subst_inf_trans_eq; apply H0.
    exists ZE_Inf; rewrite SAT1; apply H0.
    exists ZE_NegInf; rewrite SAT2; apply H0.

    (* dst part *)
    (* intros f; remember (IA.length_zform f); assert (IA.length_zform f <= n) by omega; clear Heqn; revert f H; *)
    destruct f; simpl in H; apply le_S_n in H; rewrite inf_trans_unfold; try (rewrite inf_trans_bf_dst; intuition);
    rewrite IA.dissatisfied_unfold, I2F.dissatisfied_unfold.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S1: IA.length_zform f1 <= n) by omega; assert (S2: IA.length_zform f2 <= n) by omega;
    destruct (IHn _ S1); destruct (IHn _ S2); intuition.
    assert (S: IA.length_zform f <= n) by omega; destruct (IHn _ S); intuition.

    assert (INV1: IA.length_zform (IA.substitute (v,Some ZE_Inf) f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
    assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf) f)<= n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
    destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
    split; intros; destruct H0 as [x H0]; exists x;
    assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST];
    [rewrite subst_inf_trans_eq; rewrite <- DST | rewrite DST; rewrite <- subst_inf_trans_eq]; apply H0.
    do 2 rewrite I2F.dissatisfied_unfold; split; intros.
    destruct H0 as [x H0]; destruct x.
    left; exists z; rewrite subst_inf_trans_eq.
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite <- DST; apply H0.
    right; left; rewrite <- DST1; apply H0.
    right; right; rewrite <- DST2; apply H0.
    destruct H0; destruct H0.
    exists (ZE_Fin x).
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_ZE (ZE_Fin x)) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite DST; rewrite <- subst_inf_trans_eq; apply H0.
    exists ZE_Inf; rewrite DST1; apply H0.
    exists ZE_NegInf; rewrite DST2; apply H0.

    assert (INV1: IA.length_zform (IA.substitute (v,Some ZE_Inf) f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
    assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf) f)<= n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
    destruct q; unfold PureInfinity.QT, IntToInfinity.QT.
    split; intros; assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST];
    [rewrite subst_inf_trans_eq; rewrite <- DST | rewrite DST; rewrite <- subst_inf_trans_eq]; apply H0.
    do 2 rewrite I2F.dissatisfied_unfold; split; intros.
    split; intros.
    assert (INV: IA.length_zform (IA.substitute (v, @IntToInfinity.conv tt x) f) <= n) by solve_le_inv;
    destruct (IHn _ INV) as [SAT DST].
    rewrite subst_inf_trans_eq; rewrite <- DST; apply H0.
    split; [rewrite <- DST1 | rewrite <- DST2].
    apply H0. apply H0. destruct H0 as [? [? ?]].
    destruct x.
    assert (INV: IA.length_zform (IA.substitute (v, @PureInfinity.conv PureInfinity.Q_Z z) f) <= n) by solve_le_inv;
      destruct (IHn _ INV) as [SAT DST].
    rewrite DST; rewrite <- subst_inf_trans_eq; apply H0.
    rewrite DST1; apply H1. rewrite DST2; apply H2.
  Qed.

End InfSolver.
