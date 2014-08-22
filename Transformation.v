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

  Section InfinityTransformation.

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

    Lemma inf_trans_unfold:
      forall form,
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
    Lemma subst_inf_trans_eq: forall f v (x: option ZE), I2F.substitute (v, x) (inf_trans f) =
                                                         inf_trans (IA.substitute (v, x) f).
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

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
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

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
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

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
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

      assert (INV1: IA.length_zform (IA.substitute(v,Some ZE_Inf)f) <= n) by solve_le_inv; destruct (IHn _ INV1) as [SAT1 DST1];
      assert (INV2: IA.length_zform(IA.substitute(v,Some ZE_NegInf)f)<=n) by solve_le_inv; destruct (IHn _ INV2) as [SAT2 DST2].
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

  End InfinityTransformation.

  Section IntegerTransformation.

    (* Shortened Forms of Boolean Constants *)
    Definition embed (v : Val) := FA.ZF_BF (FA.ZBF_Const v).
    Definition FATrue := embed (bool_inj true).
    Definition FAFalse := embed (bool_inj false).
    Definition FANone := embed noneVal.

    (* Projection from integers with infinity to integers *)
    Definition proj (z : IntToInfinity.N.A) : Z :=
      match z with
          Some (ZE_Fin x) => x
        | _ => 0%Z (* This case doesn't happen actually. *)
      end.

    (* Transform expressions in I2F to FA *)
    Fixpoint int_trans_exp (exp : I2F.ZExp) : FA.ZExp :=
      match exp with
          I2F.ZExp_Var v => FA.ZExp_Var v
        | I2F.ZExp_Const a => FA.ZExp_Const (proj a)
        | I2F.ZExp_Add e1 e2 => FA.ZExp_Add (int_trans_exp e1) (int_trans_exp e2)
        | I2F.ZExp_Inv e => FA.ZExp_Inv (int_trans_exp e)
        | I2F.ZExp_Sub e1 e2 => FA.ZExp_Sub (int_trans_exp e1) (int_trans_exp e2)
        | I2F.ZExp_Mult z e => FA.ZExp_Mult z (int_trans_exp e)
      end.

    (* Transform boolean forms in I2F to FA *)
    Definition int_trans_bf (bf : I2F.ZBF) : FA.ZF :=
      match bf with
          I2F.ZBF_Const f => FA.ZF_BF (FA.ZBF_Const f)
        | I2F.ZBF_Lt e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_NegInf, Some x => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some _, Some ZE_NegInf => FAFalse
            | Some ZE_Inf, Some _ => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Lt (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Lte e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some _, Some ZE_Inf => FATrue
            | Some ZE_NegInf, Some _ => FATrue
            | Some ZE_Inf, Some x => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Lte (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Gt e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_Inf, Some x => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some _, Some ZE_Inf => FAFalse
            | Some ZE_NegInf, Some _ => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Gt (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Gte e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some _, Some ZE_NegInf => FATrue
            | Some ZE_Inf, Some _ => FATrue
            | Some ZE_NegInf, Some x => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Gte (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Eq e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => FANone
            | Some ZE_NegInf, Some x
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FATrue else FAFalse
            | Some ZE_Inf, Some x
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FATrue else FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
          end
        | I2F.ZBF_Eq_Max e1 e2 e3 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2), (I2F.dexp2ZE e3) with
              None, _, _
            | _, None, _
            | _, _, None => FANone
            | Some ZE_NegInf, Some x, Some y =>
              if (ZE_eq_dec x ZE_NegInf)
              then if (ZE_eq_dec y ZE_NegInf)
                   then FATrue
                   else FAFalse
              else FAFalse
            | Some ZE_Inf, Some x, Some y =>
              if ZE_eq_dec x ZE_Inf
              then FATrue
              else if ZE_eq_dec y ZE_Inf
                   then FATrue
                   else FAFalse
            | Some (ZE_Fin _), Some ZE_NegInf, Some y =>
              match y with
                  ZE_NegInf
                | ZE_Inf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e3))
              end
            | Some (ZE_Fin _), Some y, Some ZE_NegInf =>
              match y with
                  ZE_NegInf
                | ZE_Inf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
              end
            | Some (ZE_Fin _), Some ZE_Inf, Some y
            | Some (ZE_Fin _), Some y, Some ZE_Inf => FAFalse
            | Some (ZE_Fin _), Some (ZE_Fin _), Some(ZE_Fin _) =>
              FA.ZF_BF (FA.ZBF_Eq_Max (int_trans_exp e1) (int_trans_exp e2) (int_trans_exp e3))
          end
        | I2F.ZBF_Eq_Min e1 e2 e3 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2), (I2F.dexp2ZE e3) with
              None, _, _
            | _, None, _
            | _, _, None => FANone
            | Some ZE_NegInf, Some x, Some y =>
              if ZE_eq_dec x ZE_NegInf
              then FATrue
              else if ZE_eq_dec y ZE_NegInf
                   then FATrue
                   else FAFalse
            | Some ZE_Inf, Some x, Some y =>
              if (ZE_eq_dec x ZE_Inf)
              then if (ZE_eq_dec y ZE_Inf)
                   then FATrue
                   else FAFalse
              else FAFalse
            | Some (ZE_Fin _), Some ZE_NegInf, Some y
            | Some (ZE_Fin _), Some y, Some ZE_NegInf => FAFalse
            | Some (ZE_Fin _), Some ZE_Inf, Some y =>
              match y with
                  ZE_Inf
                | ZE_NegInf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e3))
              end
            | Some (ZE_Fin _), Some y, Some ZE_Inf =>
              match y with
                  ZE_Inf
                | ZE_NegInf => FAFalse
                | _ => FA.ZF_BF (FA.ZBF_Eq (int_trans_exp e1) (int_trans_exp e2))
              end
            | Some (ZE_Fin _), Some (ZE_Fin _), Some(ZE_Fin _) =>
              FA.ZF_BF (FA.ZBF_Eq_Min (int_trans_exp e1) (int_trans_exp e2) (int_trans_exp e3))
          end
        | I2F.ZBF_Neq e1 e2 =>
          match (I2F.dexp2ZE e1), (I2F.dexp2ZE e2) with
              None, _
            | _, None => embed (truth_not noneVal)
            | Some ZE_NegInf, Some x
            | Some x, Some ZE_NegInf => if ZE_eq_dec x ZE_NegInf then FAFalse else FATrue
            | Some ZE_Inf, Some x
            | Some x, Some ZE_Inf => if ZE_eq_dec x ZE_Inf then FAFalse else FATrue
            | Some (ZE_Fin _), Some (ZE_Fin _) => FA.ZF_BF (FA.ZBF_Neq (int_trans_exp e1) (int_trans_exp e2))
          end
      end.

    (* If natural number product is finite, then either the constant is zero or the variable is finite. *)
    Lemma nat_nummult_finite: forall c v x,
                                I2F.num_mult_nat c v = Some (IntToInfinity.N.ZE_Fin x)
                                -> ((c = 0 /\ x = 0%Z) \/ (exists n, v = Some (ZE_Fin n) /\ FA.num_mult_nat c n = x)).
    Proof.
      induction c; simpl; intros.
      left; split; auto; injection H; auto.
      apply numplus_finite in H.
      destruct H, H, H.
      destruct H0.
      right; exists x0.
      split; auto.
      apply IHc in H0.
      destruct H0, H0.
      rewrite H0.
      rewrite H2 in H1.
      simpl; auto.
      destruct H0.
      assert (x2 = x0).
      rewrite H in H0.
      injection H0; auto.
      rewrite H3 in H2.
      rewrite H2; auto.
    Qed.

    (* If integer product is finite, then either the constant is zero or the variable is finite. *)
    Lemma nummult_finite: forall c v x, I2F.num_mult c v = Some (IntToInfinity.N.ZE_Fin x)
                                        -> (c = 0%Z /\ x = 0%Z) \/
                                           (exists n, v = Some (ZE_Fin n) /\ FA.num_mult c n = x).
    Proof.
      destruct c; simpl; intros.
      left; split; auto; injection H; auto.
      apply nat_nummult_finite in H.
      destruct H.
      destruct H.
      left.
      assert (0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
      omega.
      destruct H, H.
      right; exists x0.
      split; auto.
      apply numneg_finite in H.
      destruct H, H.
      apply nat_nummult_finite in H.
      destruct H.
      assert (0 < Pos.to_nat p) by apply Pos2Nat.is_pos.
      omega.
      destruct H, H.
      right; exists x1.
      split; auto.
      rewrite H1; auto.
    Qed.

    (* Expression transform from I2F to FA keeps the finiteness. *)
    Lemma dexp2ZE_int_trans_eq: forall z x, I2F.dexp2ZE z = Some (IntToInfinity.N.ZE_Fin x) -> FA.dexp2ZE (int_trans_exp z) = x.
    Proof.
      induction z; simpl; intros.
      injection H; auto.
      rewrite H; auto.
      apply numplus_finite in H;
        destruct H, H, H; destruct H0;
        apply IHz1 in H;
        apply IHz2 in H0;
        rewrite H, H0; auto.

      apply numneg_finite in H;
        destruct H, H;
        apply IHz in H;
        rewrite H; auto.

      apply numplus_finite in H;
        destruct H, H, H; destruct H0;
        apply numneg_finite in H0;
        destruct H0, H0;
        apply IHz1 in H;
        apply IHz2 in H0;
        rewrite H, H0;
        rewrite <- H2 in H1;
        auto.

      apply nummult_finite in H.
      destruct H, H.
      rewrite H, H0.
      simpl; auto.
      destruct H.
      apply IHz in H.
      rewrite H; auto.
    Qed.

    Ltac smash_int_trans_bf :=
      repeat match goal with
               | [|- context[FinRel.num_leq _ _]] => unfold FinRel.num_leq
               | [ H: FANone = _ |- _] => unfold FANone in H; unfold embed in H; inversion H; simpl
               | [|- context[truth_not (bool_inj false)]] => rewrite tautology_1
               | [|- context[truth_not (bool_inj true)]] => rewrite tautology_2
               | [|- context[truth_and ?X ?X]] => rewrite tautology_3
               | [|- context[truth_and (bool_inj true) (bool_inj false)]] => rewrite tautology_4
               | [|- context[truth_and (bool_inj false) (bool_inj true)]] => rewrite tautology_5
               | [|- context[truth_or ?X ?X]] => rewrite tautology_6
               | [|- context[truth_or (bool_inj true) (bool_inj false)]] => rewrite tautology_7
               | [|- context[truth_or (bool_inj false) (bool_inj true)]] => rewrite tautology_8
               | [|- context[truth_and noneVal (truth_not noneVal)]] => rewrite none_tautology_1
               | [|- context[truth_and noneVal (bool_inj true)]] => rewrite none_tautology_2
               | [|- context[truth_and noneVal (bool_inj false)]] => rewrite none_tautology_3
               | [|- context[truth_or noneVal (bool_inj false)]] => rewrite none_tautology_4
               | [|- context[truth_or (bool_inj false) noneVal]] => rewrite none_tautology_5
               | [H: I2F.dexp2ZE ?z = Some (IntToInfinity.N.ZE_Fin ?x) |- context[FA.dexp2ZE (int_trans_exp ?z)]]
                 => rewrite (dexp2ZE_int_trans_eq z x)
               | [|- ?X <-> ?X] => tauto
               | [H: ?X |- ?X] => apply H
               | [|- context[match (I2F.dexp2ZE ?X) with _ => _ end]] => destruct (I2F.dexp2ZE X) eqn: ?; simpl
               | [|- context[match ?X with _ => _ end]] => destruct X eqn: ?; simpl
               | [H: context[match ?X with _ => _ end] |- _] => destruct X eqn: ?; simpl
               | [|- context[InfRel.num_leq _ _]] => unfold InfRel.num_leq
               | [_: (?a <= ?b)%Z, _: ~ (?a <= ?b)%Z |- _] => contradiction
               | [_: ~ (?a <= ?b)%Z, _: ~ (?b <= ?a)%Z |- _] => exfalso; intuition
               | [|- context[truth_and (bool_inj true) noneVal]] => rewrite truth_and_comm, none_tautology_2
               | [|- context[truth_and (bool_inj false) noneVal]] => rewrite truth_and_comm, none_tautology_3
             end.

    (* Boolean transformation from I2F to FA keeps the validity. *)
    Lemma int_trans_bf_sat: forall bf, I2F.satisfied (I2F.ZF_BF bf) <-> FA.satisfied (int_trans_bf bf).
    Proof. destruct bf; simpl; rewrite I2F.satisfied_unfold, FA.satisfied_unfold; simpl; smash_int_trans_bf. Qed.

    Lemma int_trans_bf_dst: forall bf, I2F.dissatisfied (I2F.ZF_BF bf) <-> FA.dissatisfied (int_trans_bf bf).
    Proof. destruct bf; simpl; rewrite I2F.dissatisfied_unfold, FA.dissatisfied_unfold; simpl; smash_int_trans_bf. Qed.

  End IntegerTransformation.

End InfSolver.
