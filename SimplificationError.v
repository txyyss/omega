Require Import TheoryError.
Require Import TransformationError.
Require Import Bool.
Require Import Classical.

Module SimplifyProof (sv:VARIABLE) (FZT : ZERO_FIN) (IZT : ZERO_INF).
  Module ThreeVSimp := ThreeValuedSimp sv FZT IZT.
  Import sv Three_Val_NoneError ThreeVSimp InfS FA PureInt FinRel.

  Ltac solve_eqminmax :=
    repeat match goal with
             | [|- eliminateMinMax ?z <> ZF_BF _] => destruct z; simpl; intuition
             | [|- context[match judge (simplify ?f) with _ => _ end]] => destruct (judge (simplify f))
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _ _) |- _ ] => inversion H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : forall e1 e2 e3 : ZExp, simplify ?f <> ZF_BF (?X e1 e2 e3) |-
                                            simplify ?f <> ZF_BF (?X _ _ _)] => apply H
             | [|- ZF_BF (_ _) <> ZF_BF (_ _ _ _)] => discriminate
             | [|- _ _ _ <> ZF_BF _] => discriminate
             | [|- _ _ _ _ <> ZF_BF _] => discriminate
             | [|- ZF_Not _ <> ZF_BF _] => discriminate
           end.

  (* Simplification really eliminates max. *)
  Lemma simp_no_eq_max : forall f e1 e2 e3, simplify f <> ZF_BF (ZBF_Eq_Max e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  (* Simplification really eliminates min. *)
  Lemma simp_no_eq_min : forall f e1 e2 e3, simplify f <> ZF_BF (ZBF_Eq_Min e1 e2 e3).
  Proof. induction f; intros; simpl; solve_eqminmax. Qed.

  Ltac solve_error :=
    match goal with
      | [H: forall _ _ , ?X ?z1 ?z2 = ?X _ _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 = X z1 z2) by auto; destruct (H _ _ S) as [? [? M]]; discriminate M
      | [H: forall _ , ZF_Not ?z1 = ZF_Not _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : ZF_Not z1 = ZF_Not z1) by auto; destruct (H _ S) as [? M]; discriminate M
      | [H: forall _ _ _, ?X ?z1 ?z2 ?z3 = ?X _ _ _ -> _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 z3 = X z1 z2 z3) by auto; destruct (H _ _ _ S) as [? [? [? M]]]; discriminate M
      | [z: ZBF, H: ZF_BF _ <> ZF_BF _ |- _] =>
        destruct z; match goal with
                      | [H : forall _ _, ZF_BF (?X ?z ?z0) = ZF_BF (?X _ _) -> _ |- _] =>
                        let S := fresh "S" in
                        let M := fresh "M" in
                        assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto;
                          destruct (H _ _ S) as [? [? M]]; discriminate M
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Max _ _ _) |- _] => exfalso; apply simp_no_eq_max in H; apply H
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Min _ _ _) |- _] => exfalso; apply simp_no_eq_min in H; apply H
                      | [H : ZF_BF (ZBF_Const ?v0) <> ZF_BF (ZBF_Const _) |- _] =>
                        destruct v0; match goal with
                                       | [H : ?A <> ?A |- _] => exfalso; apply H; auto
                                       | [H1 : ?A <> ?B, H2: ?A = ?B |- _] => rewrite H2 in H1; exfalso; apply H1; auto
                                     end
                    end
    end.

  Ltac solve_impsb :=
    match goal with
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _ _,
                     ?X ?z1 ?z2 = ?X _ _ ->
                     exists _ _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ?X _ _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 = X z1 z2) by auto; specialize (H2 _ _ S); destruct H2 as [? [? M]];
        rewrite M in H1; discriminate H1
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _,
                     ZF_Not ?z1 = ZF_Not _ ->
                     exists _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_Not _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : ZF_Not z1 = ZF_Not z1) by auto; specialize (H2 _ S); destruct H2 as [? M];
        rewrite M in H1; discriminate H1
      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const ?A),
              H2 : forall _ _ _,
                     ?X ?z1 ?z2 ?z3 = ?X _ _ _ ->
                     exists _ _ _,
                       simplify (substitute (?v0, @conv tt ?x) ?f) = ?X _ _ _ |- _] =>
        let S := fresh "S" in
        let M := fresh "M" in
        assert (S : X z1 z2 z3 = X z1 z2 z3) by auto; specialize (H2 _ _ _ S); destruct H2 as [? [? [? M]]];
        rewrite M in H1; discriminate H1
      | [z: ZBF |- _] =>
        destruct z; match goal with
                      | [H1 : simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (ZBF_Const _),
                              H2 : forall _ _,
                                     ZF_BF (?X ?z ?z0) = ZF_BF (?X _ _) ->
                                     exists _ _,
                                       simplify (substitute (?v0, @conv tt ?x) ?f) = ZF_BF (?X _ _) |- _]
                        => let S := fresh "S" in
                           let M := fresh "M" in
                           assert (S : ZF_BF (X z z0) = ZF_BF (X z z0)) by auto; specialize (H2 _ _ S);
                           destruct H2 as [? [? M]]; rewrite M in H1; discriminate H1
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Max _ _ _) |- _] => exfalso; apply simp_no_eq_max in H; apply H
                      | [H : simplify _ = ZF_BF (ZBF_Eq_Min _ _ _) |- _] => exfalso; apply simp_no_eq_min in H; apply H
                      | [c: Val |- _] => destruct c; match goal with
                                                       | [H: ?A <> ?A |- _] => exfalso; apply H; trivial
                                                     end
                    end
    end.

  Ltac solve_same vv qq xx :=
    repeat match goal with
             | [|- _ /\ _] => split
             | [|- _ -> _ ] => intros
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_BF _ |- _] => destruct z; simpl in *
             | [H : ZF_BF (_ _ _) = ZF_BF (ZBF_Const _) |- _] => inversion H
             | [H : ?X |- ?X] => apply H
             | [H : _ _ _ = ZF_BF _ |- _] => inversion H
             | [H : ZF_BF (_ _) = ZF_BF (_ _ _) |- _] => inversion H
             | [H : ZF_BF (_ _ _) = ZF_BF (_ _ _) |- _] => discriminate H
             | [|- exists e3 e4 : ZExp, ZF_BF (?X ?A ?B) = ZF_BF (?X e3 e4)] => exists A, B
             | [|- ?A = ?A] => auto
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_And _ _ |- _] => destruct z; simpl in *
             | [H : _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ |- _] => discriminate H
             | [H : ZF_BF _ = ZF_Not _ |- _] => discriminate H
             | [H : ZF_Not _ = ZF_BF _ |- _] => discriminate H
             | [H : _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ = _ _ _ _ |- _] => discriminate H
             | [H : _ _ _ _ = _ _ |- _] => discriminate H
             | [H : _ _ _ _ = _ _ _ |- _] => discriminate H
             | [H : ZF_Forall _ _ _ = ZF_Exists _ _ _ |- _] => discriminate H
             | [H : ZF_Exists _ _ _ = ZF_Forall _ _ _ |- _] => discriminate H
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Or _ _ |- _] => destruct z; simpl in *
             | [|- exists f3 f4 : ZF, ?X ?A ?B = ?X f3 f4] => exists A, B; auto
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Imp _ _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Not _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Forall _ _ _ |- _] => destruct z; simpl in *
             | [z: ZBF, H: simplify (ZF_BF _) = ZF_Exists _ _ _ |- _] => destruct z; simpl in *
             | [H : forall (q : Q) (x : QT q) (v : var), _ |- _ ] =>
               specialize (H qq xx); destruct (H vv) as [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]
             | [H : simplify (ZF_And _ _) = _ |- _] => simpl in H
             | [H : context[match judge ?X with _ => _ end] |- _] => destruct (judge X)
             | [H1 : forall c : Val, simplify ?f1 = ZF_BF (ZBF_Const c) -> _ ,
                  H2 : simplify ?f1 = ZF_BF (ZBF_Const _) |- _] => specialize (H1 _ H2)
             | [|- simplify (substitute _ (ZF_And _ _)) = _] => simpl
             | [|- context[match judge ?X with _ => _ end]] => destruct (judge X)
             | [H1: simplify (substitute ?A ?f) = _, H2: simplify (substitute ?A ?f) = _ |- _] =>
               rewrite H1 in *
             | [H : ?A = ?B |- ?B = ?A ] => rewrite <- H; auto
             | [H : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VFalse) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VError) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VFalse) = ZF_BF (ZBF_Const VTrue) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VFalse) = ZF_BF (ZBF_Const VError) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VError) = ZF_BF (ZBF_Const VTrue) |- _] => discriminate H
             | [H : ZF_BF (ZBF_Const VError) = ZF_BF (ZBF_Const VFalse) |- _] => discriminate H
             | [H : ?A = _ |- context[?A]] => rewrite H in *
             | [H : ?A = _, H2: context[?A] |- _] => rewrite H in *
             | [H : _ /\ _ |- _] => destruct H
             | [H : ?A <> ?A |- _] => exfalso; apply H; auto
             | [H : simplify ?f2 <> ZF_BF (ZBF_Const _), H2 : forall _ _, simplify ?f2 = ZF_And _ _ -> _ |- _] =>
               destruct (simplify f2) eqn: ?; solve_error
             | [|- context[simplify (substitute _ (ZF_And _ _))]] => simpl
             | [H : (forall _ _, ZF_BF (?X ?e1 ?e2) = ZF_BF (?X _ _) -> exists _ _, ?Y = ZF_BF (?X _ _))
                |- exists _ _, ?Y = ZF_BF (?X _ _)] =>
               let S := fresh "S" in assert (S : ZF_BF (X e1 e2) = ZF_BF (X e1 e2)) by auto; apply (H _ _ S)
             | [H : (forall _ _, ?X ?f0 ?f3 = ?X _ _ -> exists _ _, ?Y = ?X _ _) |- exists _ _, ?Y = ?X _ _]
               => let S := fresh "S" in assert (S : X f0 f3 = X f0 f3) by auto; apply (H _ _ S)
             | [H : (forall _, ?X ?f0 = ?X _ -> exists _, ?Y = ?X _) |- exists _, ?Y = ?X _]
               => let S := fresh "S" in assert (S : X f0 = X f0) by auto; apply (H _ S)
             | [H : (forall _ _ _, ?X ?f0 ?f3 ?f4 = ?X _ _ _ -> exists _ _ _, ?Y = ?X _ _ _)
                |- exists _ _ _, ?Y = ?X _ _ _]
               => let S := fresh "S" in assert (S : X f0 f3 f4 = X f0 f3 f4) by auto; apply (H _ _ _ S)
             | [H : simplify (ZF_Or _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Or _ _))]] => simpl
             | [H : simplify (ZF_Imp _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Imp _ _))]] => simpl
             | [|- exists f3 : ZF, ZF_Not ?A = ZF_Not f3] => exists A; auto
             | [H : simplify (ZF_Not _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Not _))]] => simpl
             | [H : simplify (ZF_Forall _ _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Forall _ _ _))]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplify (ZF_Forall _ _ _)]] => simpl
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c), H : ZF_BF (ZBF_Const ?A) = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) = ZF_BF (ZBF_Const ?B), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; rewrite <- H in * |-; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const A) = ZF_BF (ZBF_Const A)) by auto; specialize (HC _ S);
               rewrite HC in e0; discriminate e0
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) <> ZF_BF (ZBF_Const ?c), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const VTrue) = ZF_BF (ZBF_Const VTrue)) by auto;
               specialize (HC _ S); rewrite HC in e0; exfalso; apply e0; trivial
             | [q : Q, q0 : Q, e : simplify ?f = ZF_BF (ZBF_Const ?c),
                e0 : simplify (substitute (?v0, conv ?x) ?f) <> ZF_BF (ZBF_Const ?c), IHf : forall _ : var, _ |- _] =>
               let HC := fresh "HC" in
               let S := fresh "S" in
               destruct q; destruct q0; destruct (IHf v0) as [HC _];
               assert (S : ZF_BF (ZBF_Const c) = ZF_BF (ZBF_Const c)) by auto;
               specialize (HC _ S); rewrite HC in e0; exfalso; apply e0; trivial
             | [|- exists (v2 : var) (q2 : Q) (f2 : ZF), ?X ?v1 ?q1 ?f1 = ?X v2 q2 f2] =>
               exists v1, q1, f1; trivial
             | [q : Q, q0 : Q, q1 : Q, H1: simplify (substitute (?v0, conv ?x) ?f) = ZF_BF (ZBF_Const ?A),
                                           H13 : simplify ?f <> ZF_BF (ZBF_Const ?A), IHf: forall _ : var, _ |- _] =>
               destruct q, q0, q1; destruct (IHf v0) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]];
               destruct (simplify f) eqn : ?; solve_impsb
             | [H : simplify (ZF_Exists _ _ _) = _ |- _] => simpl in H
             | [|- context[simplify (substitute _ (ZF_Exists _ _ _))]] => simpl
             | [|- context[simplify (ZF_Exists _ _ _)]] => simpl
           end.

  (* Substitution doesn't change the form of simplified result *)
  Lemma simp_subst_the_same:
    forall f q (x : QT q) v,
      (forall c, simplify f = ZF_BF (ZBF_Const c) -> simplify (substitute (v, conv x) f) = ZF_BF (ZBF_Const c)) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Lt e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Lt e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Lte e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Lte e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Gt e1 e2) ->
                     (exists e3 e4, simplify (substitute (v,conv x) f) = ZF_BF(ZBF_Gt e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Gte e1 e2) ->
                     (exists e3 e4, simplify(substitute (v,conv x) f) = ZF_BF(ZBF_Gte e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Eq e1 e2) ->
                     (exists e3 e4, simplify(substitute (v, conv x) f) = ZF_BF (ZBF_Eq e3 e4))) /\
      (forall e1 e2, simplify f = ZF_BF (ZBF_Neq e1 e2) ->
                     (exists e3 e4, simplify (substitute (v, conv x) f) = ZF_BF (ZBF_Neq e3 e4))) /\
      (forall f1 f2, simplify f = ZF_And f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_And f3 f4)) /\
      (forall f1 f2, simplify f = ZF_Or f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_Or f3 f4)) /\
      (forall f1 f2, simplify f = ZF_Imp f1 f2 -> (exists f3 f4, simplify (substitute (v, conv x) f) = ZF_Imp f3 f4)) /\
      (forall f1, simplify f = ZF_Not f1 -> (exists f2, simplify (substitute (v, conv x) f) = ZF_Not f2)) /\
      (forall v1 q1 f1, simplify f = ZF_Forall v1 q1 f1->
                        (exists v2 q2 f2, simplify (substitute (v, conv x) f) = ZF_Forall v2 q2 f2)) /\
      (forall v1 q1 f1, simplify f = ZF_Exists v1 q1 f1->
                        (exists v2 q2 f2, simplify (substitute (v, conv x) f) = ZF_Exists v2 q2 f2)).
  Proof. induction f; intros; solve_same v q x. Qed.

  (* simplification and substitution are commutative. *)
  Lemma simp_subst_comm: forall f v q (x : QT q), substitute (v, conv x) (simplify f) = simplify (substitute (v, conv x) f).
  Proof.
    induction f; intros; simpl substitute at 2; simpl; try (destruct z; simpl; auto);
    repeat match goal with
             | [|- context[match judge (simplify ?A) with _ => _ end]] => destruct (judge (simplify A))
             | [H : ?A = _ |- context[?A]] => rewrite H
             | [|- substitute (_, conv _) (ZF_BF (ZBF_Const ?A)) = ZF_BF (ZBF_Const ?A)] => simpl; auto
             | [H1: simplify ?f = ZF_BF (ZBF_Const _),
                    H2: simplify (substitute (?v, @conv ?q ?x) ?f) = ZF_BF (ZBF_Const _) |- _]
               => let H := fresh "H" in
                  destruct (simp_subst_the_same f q x v) as [H _]; specialize (H _ H1); rewrite H in H2; discriminate H2
             | [H : _ /\ _ |- _] => destruct H
             | [H1: simplify ?f = ZF_BF (ZBF_Const ?A),
                    H2: simplify (substitute (?v, @conv ?q ?x) ?f) <> ZF_BF (ZBF_Const ?A) |- _]
               => let H := fresh "H" in
                  destruct (simp_subst_the_same f q x v) as [H _]; specialize (H _ H1); rewrite H in H2; exfalso; apply H2; auto
             | [H1: simplify ?f <>ZF_BF(ZBF_Const ?A), H2:simplify (substitute (?v, @conv ?q ?x) ?f) = ZF_BF(ZBF_Const ?A) |- _]
               => destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]]; rewrite H2 in *;
                  destruct (simplify f) eqn : ?; solve_error
             | [H: forall _ _ _ , substitute _ (simplify ?f) = _ |- context[substitute _ (simplify ?f)]] => rewrite H
             | [|- ?A = ?A] => trivial
             | [|- context[substitute _ (ZF_And _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Or _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Imp _ _) ]] => simpl
             | [|- context[substitute _ (ZF_Not _) ]] => simpl
             | [|- context[var_eq_dec ?v0 ?v]] => destruct (var_eq_dec v0 v)
             | [|- context[simplify (ZF_Forall _ _ _)]] => simpl
             | [H1: ?A = _, H2: ?A = _ |- _] => rewrite H1 in H2
             | [H1: ?A = _, H2: ?A <> _ |- _] => rewrite H1 in H2
             | [H: ?A <> ?A |- _] => exfalso; apply H; trivial
             | [|- context[simplify (ZF_Exists _ _ _)]] => simpl
           end.
  Qed.

  Definition hasError_bf (bf : ZBF) := match bf with | ZBF_Const VError => true | _ => false end.

  Fixpoint hasError (f : ZF) :=
    match f with
      | ZF_BF bf => hasError_bf bf
      | ZF_And f1 f2 => hasError f1 || hasError f2
      | ZF_Or f1 f2 => hasError f1 || hasError f2
      | ZF_Imp f1 f2 => hasError f1 || hasError f2
      | ZF_Not ff => hasError ff
      | ZF_Forall _ _ ff => hasError ff
      | ZF_Exists _ _ ff => hasError ff
    end.

  Definition no_error (f : ZF) := hasError f = false.

  Definition no_error_dec: forall f, {no_error f} + {~ no_error f}.
    intros. destruct (bool_dec (hasError f) false); [left | right]. apply e. apply n.
  Defined.

  Ltac solve_prgtn :=
    repeat match goal with
             | [H: ?A |- ?A] => apply H
             | [H1: ?A = _, H2: context[?A] |- _] => rewrite H1 in H2
             | [H: ZF_BF (ZBF_Const _) = ZF_BF (ZBF_Const _) |- _] => discriminate H
             | [H: _ /\ _ |- _] => destruct H
             | [H: ?A <> ?A |- _] => exfalso; apply H; trivial
    end.

  Lemma error_propagation: forall f, ~ no_error f -> simplify f = ZF_BF (ZBF_Const VError).
  Proof.
    induction f; intros; unfold no_error in * |-; simpl in H.
    destruct z; simpl in H; first [destruct v; intuition | intuition].
    apply not_false_is_true in H. apply orb_true_iff in H. destruct H; apply not_false_iff_true in H.
    specialize (IHf1 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    specialize (IHf2 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    apply not_false_is_true in H. apply orb_true_iff in H. destruct H; apply not_false_iff_true in H.
    specialize (IHf1 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    specialize (IHf2 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    apply not_false_is_true in H. apply orb_true_iff in H. destruct H; apply not_false_iff_true in H.
    specialize (IHf1 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    specialize (IHf2 H); simpl; destruct (judge (simplify f1)); destruct (judge (simplify f2)); solve_prgtn.
    specialize (IHf H); simpl; destruct (judge (simplify f)); solve_prgtn.
    specialize (IHf H); simpl; destruct (judge (simplify f)); solve_prgtn.
    specialize (IHf H); simpl; destruct (judge (simplify f)); solve_prgtn.
  Qed.

  Lemma eq_and_le_satdst_1 : forall z z0 z1, satisfied (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z1 z0))) \/
                                             dissatisfied (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z1 z0))).
  Proof.
    intros; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold; repeat rewrite satisfied_unfold;
    simpl; unfold num_leq; destruct (ZArith_dec.Z_le_dec (dexp2ZE z) (dexp2ZE z0));
    destruct (ZArith_dec.Z_le_dec (dexp2ZE z0) (dexp2ZE z)), (ZArith_dec.Z_le_dec (dexp2ZE z1) (dexp2ZE z0)); simpl; tauto.
  Qed.

  Lemma eq_and_le_satdst_2 : forall z z0 z1, satisfied (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z0 z1))) \/
                                             dissatisfied (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z0 z1))).
  Proof.
    intros; repeat rewrite satisfied_unfold; repeat rewrite dissatisfied_unfold; repeat rewrite satisfied_unfold;
    simpl; unfold num_leq; destruct (ZArith_dec.Z_le_dec (dexp2ZE z) (dexp2ZE z0));
    destruct (ZArith_dec.Z_le_dec (dexp2ZE z0) (dexp2ZE z)), (ZArith_dec.Z_le_dec (dexp2ZE z0) (dexp2ZE z1)); simpl; tauto.
  Qed.

  Lemma eliminate_undet: forall z, undetermined (eliminateMinMax z) -> eliminateMinMax z = ZF_BF (ZBF_Const VError).
  Proof.
    intros; destruct z; simpl; rewrite undetermined_unfold, satisfied_unfold, dissatisfied_unfold in H; simpl in H;
    repeat match goal with
             | [H : _ /\ _ |- _] => destruct H
             | [c : Val |- _] => destruct c
             | [H : VTrue <> Top |- _] => exfalso; apply H; trivial
             | [H : VFalse <> Btm |- _] => exfalso; apply H; trivial
             | [|- ?A = ?A] => trivial
             | [H : context[num_leq _ _] |- _] => unfold num_leq in H
             | [H : context[ZArith_dec.Z_le_dec ?x ?y] |- _] => destruct (ZArith_dec.Z_le_dec x y)
             | [H : context[truth_and _ _] |- _] => simpl in H
             | [H : ?A <> ?A |- _] => exfalso; apply H; trivial
           end.
    Ltac solve_2nd := repeat match goal with
                               | [H1: ~ ?A, H2: ?A |- False] => apply H1, H2
                               | [H: ~ (_ \/ _) |- _] => apply not_or_and in H
                               | [H: _ /\ _ |- _] => destruct H
                               | [H: ~ (_ /\ _) |- _] => apply not_and_or in H
                               | [H: _ \/ _ |- _] => destruct H
                             end.
    remember (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z1 z0))); destruct (eq_and_le_satdst_1 z z0 z1);
    remember (ZF_And (ZF_BF (ZBF_Eq z z1)) (ZF_BF (ZBF_Lte z0 z1))); destruct (eq_and_le_satdst_1 z z1 z0);
    rewrite <- Heqz2 in H1; rewrite <- Heqz3 in H2; clear Heqz2 Heqz3 z z0 z1; exfalso; solve_2nd.
    remember (ZF_And (ZF_BF (ZBF_Eq z z0)) (ZF_BF (ZBF_Lte z0 z1))); destruct (eq_and_le_satdst_2 z z0 z1);
    remember (ZF_And (ZF_BF (ZBF_Eq z z1)) (ZF_BF (ZBF_Lte z1 z0))); destruct (eq_and_le_satdst_2 z z1 z0);
    rewrite <- Heqz2 in H1; rewrite <- Heqz3 in H2; clear Heqz2 Heqz3 z z0 z1; exfalso; solve_2nd.
  Qed.

  Ltac solve_udt :=
    repeat match goal with
             | [H : VTrue <> Top |- _] => exfalso; apply H; trivial
             | [H : VFalse <> Btm |- _] => exfalso; apply H; trivial
             | [H1: ~ ?A, H2: ?A |- _] => exfalso; apply H1, H2
             | [H1: ?A -> ?B, H2: ?A |- ?B] => apply H1; apply H2
             | [|- ?A = ?A] => trivial
             | [H: undetermined (ZF_BF _) |- _] =>
               rewrite undetermined_unfold, satisfied_unfold, dissatisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_And _ _) |- _] =>
               rewrite undetermined_unfold, satisfied_unfold, dissatisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_Or _ _) |- _] =>
               rewrite undetermined_unfold, dissatisfied_unfold, satisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_Imp _ _) |- _] =>
               rewrite undetermined_unfold, dissatisfied_unfold, satisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_Not _) |- _] =>
               rewrite undetermined_unfold, dissatisfied_unfold, satisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_Forall _ _ _) |- _] =>
               rewrite undetermined_unfold, dissatisfied_unfold, satisfied_unfold in H; simpl in H; destruct H
             | [H: undetermined (ZF_Exists _ _ _) |- _] =>
               rewrite undetermined_unfold, dissatisfied_unfold, satisfied_unfold in H; simpl in H; destruct H
             | [H : _ /\ _ |- _] => destruct H
             | [H: ~ (_ \/ _) |- _] => apply not_or_and in H
             | [H: ~ (_ /\ _) |- _] => apply not_and_or in H
             | [H1: _ -> ?A = ?B, H2: ?A <> ?B |- _] => destruct (imply_to_or _ _ H1); clear H1
             | [H: ~ undetermined (simplify _) |- _] => rewrite undetermined_unfold in H
             | [H: ~ ~ _ \/ ~ ~ _ |- _] => destruct H
             | [H: ~ ~ _ |- _] => apply NNPP in H
             | [H: _ \/ _ |- _] => destruct H
             | [H: ~ (forall _, _) |- _] => apply not_all_ex_not in H
           end.

  Ltac solve_satdst :=
    repeat match goal with
             | [|- _ /\ _ ] => split
             | [H: _ /\ _ |- _] => destruct H
             | [H: ?A = _ |- context[?A]] => rewrite H
             | [|- context[satisfied (ZF_BF (ZBF_Const _))]] =>
               repeat rewrite satisfied_unfold; repeat rewrite <- satisfied_unfold; simpl
             | [|- context[dissatisfied (ZF_BF (ZBF_Const _))]] =>
               repeat rewrite dissatisfied_unfold; repeat rewrite <- dissatisfied_unfold; simpl
             | [|- _ <-> _] => split; intros
             | [H: _ \/ _ |- _] => destruct H
             | [H: VTrue = Btm |- _] => discriminate H
             | [H: VError = Btm |- _] => discriminate H
             | [H: VError = Top |- _] => discriminate H
             | [H: VFalse = Top |- _] => discriminate H
             | [|- ?A = ?A] => trivial
             | [|- _ \/ ?A = ?A] => right; trivial
             | [|- VFalse = Btm] => trivial
             | [|- VTrue = Top] => trivial
             | [H: ?A |- ?A] => apply H
             | [H: ?A |- _ \/ ?A ] => right; trivial
             | [|- VFalse = Btm \/ _] => left; trivial
             | [H: ?A |- ?A \/ _ ] => left; trivial
             | [|- context[Top = Top]] => tauto
             | [|- context[Btm = Btm]] => tauto
             | [H: ?A |- VTrue = Top /\ ?A \/ _ \/ _] => left; intuition
             | [|- _ \/ _ \/ VFalse = Btm /\ VFalse = Btm] => right; right; tauto
             | [H: ?A |- _ \/ VFalse = Btm /\ ?A \/ _] => right; left; intuition
             | [H: ?A |- _ \/ VTrue = Top /\ ?A \/ _] => right; left; intuition
             | [H: ?A |- _ \/ _ \/ VFalse = Btm /\ ?A] => right; right; intuition
             | [H1: ?A = ?B, H2: ?A <> ?B |- _] => exfalso; apply H2, H1
             | [H1: satisfied ?A, H2: dissatisfied ?A |- _] => exfalso; apply (sat_dissat_disj A); intuition
             | [H: ?A |- _ \/ _ \/ ?A /\ VFalse = Btm] => right; right; intuition
             | [H: ?A |- _ \/ _ \/ ?A /\ VTrue = Top] => right; right; intuition
             | [|- context[satisfied (ZF_And _ _)]] =>
               repeat rewrite satisfied_unfold; repeat rewrite <- satisfied_unfold
             | [|- context[satisfied (ZF_Or _ _)]] =>
               repeat rewrite satisfied_unfold; repeat rewrite <- satisfied_unfold
             | [|- context[satisfied (ZF_Imp _ _)]] =>
               repeat rewrite satisfied_unfold; repeat rewrite <- satisfied_unfold
             | [|- context[satisfied (ZF_Not _)]] =>
               repeat rewrite satisfied_unfold; repeat rewrite <- satisfied_unfold
             | [H1: ?A, H2: ?B |- ?A /\ ?B \/ _] => left; intuition
             | [H1: ?A, H2: ?B |- _ \/ ?A /\ ?B \/ _] => right; left; intuition
             | [H1: ?A, H2: ?B |- _ \/ _ \/ ?A /\ ?B] => right; right; intuition
             | [H: context[dissatisfied (ZF_And _ _)] |- _] =>
               repeat rewrite dissatisfied_unfold in H; repeat rewrite <- dissatisfied_unfold in H
             | [H: context[dissatisfied (ZF_Or _ _)] |- _] =>
               repeat rewrite dissatisfied_unfold in H; repeat rewrite <- dissatisfied_unfold in H
             | [H: context[dissatisfied (ZF_Imp _ _)] |- _] =>
               repeat rewrite dissatisfied_unfold in H; repeat rewrite <- dissatisfied_unfold in H
             | [H: context[dissatisfied (ZF_Not _)] |- _] =>
               repeat rewrite dissatisfied_unfold in H; repeat rewrite <- dissatisfied_unfold in H
             | [H: context[satisfied (ZF_And _ _)] |- _] =>
               repeat rewrite satisfied_unfold in H; repeat rewrite <- satisfied_unfold in H
             | [H: context[satisfied (ZF_Or _ _)] |- _] =>
               repeat rewrite satisfied_unfold in H; repeat rewrite <- satisfied_unfold in H
             | [H: context[satisfied (ZF_Imp _ _)] |- _] =>
               repeat rewrite satisfied_unfold in H; repeat rewrite <- satisfied_unfold in H
             | [H: context[satisfied (ZF_Not _)] |- _] =>
               repeat rewrite satisfied_unfold in H; repeat rewrite <- satisfied_unfold in H
             | [|- context[dissatisfied (ZF_And _ _)]] =>
               repeat rewrite dissatisfied_unfold; repeat rewrite <- dissatisfied_unfold
             | [|- context[dissatisfied (ZF_Or _ _)]] =>
               repeat rewrite dissatisfied_unfold; repeat rewrite <- dissatisfied_unfold
             | [|- context[dissatisfied (ZF_Imp _ _)]] =>
               repeat rewrite dissatisfied_unfold; repeat rewrite <- dissatisfied_unfold
             | [|- context[dissatisfied (ZF_Not _)]] =>
               repeat rewrite dissatisfied_unfold; repeat rewrite <- dissatisfied_unfold
             | [H1: _ -> ?A = ?B, H2: ?A = ?B -> False |- _] => destruct (imply_to_or _ _ H1); clear H1
             | [H1: _ -> ?A = ?B, H2: ?A <> ?B |- _] => destruct (imply_to_or _ _ H1); clear H1
             | [H: ~ undetermined (simplify _) |- _] => rewrite undetermined_unfold in H
             | [H: ~ (_ /\ _) |- _] => apply not_and_or in H
             | [H: ~ ~ _ \/ ~ ~ _ |- _] => destruct H
             | [H: ~ ~ _ |- _] => apply NNPP in H
           end.

  Ltac assertSS f x q v n :=
    let SS := fresh "SS" in
    let S := fresh "S" in
    let MM := fresh "MM" in
    assert (SS : (substitute (@pair var N.A v (@conv q x)) (simplify f)) =
                 (simplify (substitute (@pair var N.A v (@conv q x)) f))) by apply simp_subst_comm;
    assert (S : length_zform (substitute (@pair var N.A v (@conv q x)) f) <= n) by
        (rewrite <- substitute_length_inv; assumption);
    assert (MM : (simplify (substitute (@pair var (QT q) v (@conv q x)) f)) =
                 (simplify (substitute (@pair var N.A v (@conv q x)) f))) by auto.

  (* Simplification keeps the validity. *)
  Lemma simplify_ok: forall f, (undetermined (simplify f) -> simplify f = ZF_BF (ZBF_Const VError)) /\
                               (satisfied f <-> satisfied (simplify f)) /\
                               (dissatisfied f <-> dissatisfied (simplify f)).

  Proof.
    intros; remember (length_zform f); assert (length_zform f <= n) by omega; clear Heqn; revert f H; induction n; intros.
    exfalso; destruct f; simpl in H; omega.
    destruct f; simpl; first[split; [apply eliminate_undet | apply eliminate_ok] | simpl in H; apply le_S_n in H].

    assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [UDT1 [SAT1 DST1]]; destruct (IHn _ S2) as [UDT2 [SAT2 DST2]]; clear IHn; split.
    destruct (judge (simplify f1)), (judge (simplify f2)); intros; solve_udt.
    rewrite satisfied_unfold; rewrite dissatisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 n; destruct (judge (simplify f1)), (judge (simplify f2)); solve_satdst.

    assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [UDT1 [SAT1 DST1]]; destruct (IHn _ S2) as [UDT2 [SAT2 DST2]]; clear IHn; split.
    destruct (judge (simplify f1)), (judge (simplify f2)); intros; solve_udt.
    rewrite dissatisfied_unfold; rewrite satisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 n; destruct (judge (simplify f1)), (judge (simplify f2)); solve_satdst.

    assert (S1 : length_zform f1 <= n) by omega; assert (S2 : length_zform f2 <= n) by omega;
    destruct (IHn _ S1) as [UDT1 [SAT1 DST1]]; destruct (IHn _ S2) as [UDT2 [SAT2 DST2]]; clear IHn; split.
    destruct (judge (simplify f1)), (judge (simplify f2)); intros; solve_udt.
    rewrite dissatisfied_unfold; rewrite satisfied_unfold; rewrite SAT1, SAT2, DST1, DST2;
    clear H S1 S2 SAT1 SAT2 DST1 DST2 n; destruct (judge (simplify f1)), (judge (simplify f2)); solve_satdst.

    assert (S : length_zform f <= n) by omega; destruct (IHn _ S) as [UDT [SAT DST]]; clear IHn; split.
    destruct (judge (simplify f)); intros; solve_udt.
    rewrite dissatisfied_unfold; rewrite satisfied_unfold; rewrite SAT, DST;
    clear H S SAT DST n; destruct (judge (simplify f)); solve_satdst.

    (* forall 1st part *)

    split.
    destruct (judge (simplify f)); intros; solve_udt; destruct H0 as [x H0];
    assert (SS : (substitute (@pair var N.A v (@conv q x)) (simplify f)) =
                 (simplify (substitute (@pair var N.A v (@conv q x)) f))) by apply simp_subst_comm;
    assert (S : length_zform (substitute (@pair var N.A v (@conv q x)) f) <= n) by
        (rewrite <- substitute_length_inv; assumption);
    destruct (IHn _ S) as [UDT [_ _]]; clear S; destruct (imply_to_or _ _ UDT);
    clear UDT; rewrite <- SS in *.
    exfalso; apply H1; clear H1.
    rewrite undetermined_unfold in H5; apply not_and_or in H5; destruct H5.
    apply NNPP in H1. exfalso; apply H0, H1.
    apply NNPP in H1. exists x; apply H1.
    rewrite SS in H5. destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    assert (MM : (simplify (substitute (@pair var (QT q) v (@conv q x)) f)) =
                 (simplify (substitute (@pair var N.A v (@conv q x)) f))) by auto.
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.

    destruct H1 as [xn H1]; apply not_or_and in H1; destruct H1.
    clear H0 SS H5 x.
    assert (SS : (substitute (@pair var N.A v (@conv q xn)) (simplify f)) =
                 (simplify (substitute (@pair var N.A v (@conv q xn)) f))) by apply simp_subst_comm;
    assert (S : length_zform (substitute (@pair var N.A v (@conv q xn)) f) <= n) by
        (rewrite <- substitute_length_inv; assumption).
    specialize (IHn _ S); destruct IHn as [UDT _]. clear S; destruct (imply_to_or _ _ UDT); clear UDT; rewrite <- SS in H0.
    rewrite undetermined_unfold in H0; apply not_and_or in H0; destruct H0; apply NNPP in H0.
    exfalso; apply H1, H0. exfalso; apply H6, H0.
    rewrite SS in H0. destruct (simp_subst_the_same f q xn v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    assert (MM : (simplify (substitute (@pair var (QT q) v (@conv q xn)) f)) =
                 (simplify (substitute (@pair var N.A v (@conv q xn)) f))) by auto.
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H0; discriminate H0.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H0; discriminate H0.

    rewrite SS in H5. destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    assert (MM : (simplify (substitute (@pair var (QT q) v (@conv q x)) f)) =
                 (simplify (substitute (@pair var N.A v (@conv q x)) f))) by auto.
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.

    (* forall rest part *)
    destruct (judge (simplify f)); intros; split; split; intros;
    repeat match goal with
             | [|- satisfied (ZF_BF (ZBF_Const VTrue))] => rewrite satisfied_unfold; simpl; trivial
             | [|- dissatisfied (ZF_BF (ZBF_Const VFalse))] => rewrite dissatisfied_unfold; simpl; trivial
             | [H: dissatisfied (ZF_BF (ZBF_Const VTrue)) |- _] => rewrite dissatisfied_unfold in H; simpl in H; discriminate H
             | [H: satisfied (ZF_BF (ZBF_Const VFalse)) |- _] => rewrite satisfied_unfold in H; simpl in H; discriminate H
             | [H: satisfied (ZF_BF (ZBF_Const VError)) |- _] => rewrite satisfied_unfold in H; simpl in H; discriminate H
             | [H: dissatisfied (ZF_BF (ZBF_Const VError)) |- _] => rewrite dissatisfied_unfold in H; simpl in H; discriminate H
             | [H: _ /\ _ |- _] => destruct H
           end.
    rewrite satisfied_unfold; intros; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]]; apply SAT;
    destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M; rewrite M;
    rewrite satisfied_unfold; simpl; trivial.

    rewrite dissatisfied_unfold in H0; destruct H0 as [[x ?] ?]; assertSS f x q v n; destruct (IHn _ S) as [_ [_ DST]];
    apply DST in H0; destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite dissatisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite satisfied_unfold in H0; specialize (H0 N.Const0); assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [SAT _]];
    apply SAT in H0; destruct (simp_subst_the_same f q N.Const0 v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite satisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite dissatisfied_unfold; split;
    [exists N.Const0; assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [_ DST]]; apply DST;
            destruct (simp_subst_the_same f q N.Const0 v) as [M _] |
            intros; right; assertSS f x q v n; destruct (IHn _ S) as [_ [_ DST]]; apply DST;
            destruct (simp_subst_the_same f q x v) as [M _]]; specialize (M _ e); rewrite MM in M; rewrite M;
    rewrite dissatisfied_unfold; simpl; trivial.

    rewrite satisfied_unfold in H0; specialize (H0 N.Const0); assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [SAT _]];
    apply SAT in H0; destruct (simp_subst_the_same f q N.Const0 v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite satisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite dissatisfied_unfold in H0; destruct H0 as [[x ?] ?]; assertSS f x q v n; destruct (IHn _ S) as [_ [_ DST]];
    apply DST in H0; destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite dissatisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite satisfied_unfold in H0; rewrite satisfied_unfold; intros; specialize (H0 x); assertSS f x q v n;
    destruct (IHn _ S) as [_ [SAT _]]; apply SAT in H0; rewrite <- SS in H0; apply H0.

    rewrite satisfied_unfold in H0; rewrite satisfied_unfold; intros; specialize (H0 x); assertSS f x q v n;
    destruct (IHn _ S) as [_ [SAT _]]; rewrite SAT; rewrite <- SS; apply H0.


    rewrite dissatisfied_unfold in H0; rewrite dissatisfied_unfold; destruct H0; split.
    destruct H0 as [x H0]; exists x; assertSS f x q v n; destruct (IHn _ S) as [_ [_ DST]]; rewrite SS; apply DST, H0.
    intros; specialize (H4 x); assertSS f x q v n; destruct (IHn _ S) as [_ [SAT DST]]; rewrite SS;
    destruct H4; [left; apply SAT | right; apply DST]; apply H4.

    rewrite dissatisfied_unfold in H0; rewrite dissatisfied_unfold; destruct H0; split.
    destruct H0 as [x H0]; exists x; assertSS f x q v n; destruct (IHn _ S) as [_ [_ DST]]; rewrite SS in H0; apply DST, H0.
    intros; specialize (H4 x); assertSS f x q v n; destruct (IHn _ S) as [_ [SAT DST]]; rewrite SS in H4;
    destruct H4; [left; apply SAT | right; apply DST]; apply H4.

    (* exists 1st part *)
    split.
    destruct (judge (simplify f)); intros; solve_udt; destruct H1 as [x H1]; assertSS f x q v n;
    destruct (IHn _ S) as [UDT [_ _]]; clear S; destruct (imply_to_or _ _ UDT); clear UDT; rewrite <- SS in *.
    rewrite undetermined_unfold in H5; apply not_and_or in H5; destruct H5; apply NNPP in H5.
    exfalso; apply H0; exists x; apply H5. exfalso; apply H1, H5.
    rewrite SS in H5. destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.

    clear H1 SS MM H5 x. destruct H0 as [x H0]; apply not_or_and in H0; destruct H0. assertSS f x q v n.
    specialize (IHn _ S); destruct IHn as [UDT _]. clear S; destruct (imply_to_or _ _ UDT); clear UDT.
    rewrite undetermined_unfold in H5; apply not_and_or in H5; destruct H5; apply NNPP in H5; rewrite <- SS in H5.
    exfalso; apply H0, H5. exfalso; apply H1, H5.

    destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite M in H5; discriminate H5.

    rewrite SS in H5. destruct (simp_subst_the_same f q x v) as [?[?[?[?[?[?[?[?[?[?[?[? ?]]]]]]]]]]]].
    destruct (simplify f) eqn: ?. destruct z. destruct v0; exfalso.
    apply H2; auto. apply H3; auto. apply H4; auto.
    assert (S : ZF_BF (ZBF_Lt z z0) = ZF_BF (ZBF_Lt z z0)) by auto; specialize (H7 _ _ S); destruct H7 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Lte z z0) = ZF_BF (ZBF_Lte z z0)) by auto; specialize (H8 _ _ S); destruct H8 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gt z z0) = ZF_BF (ZBF_Gt z z0)) by auto; specialize (H9 _ _ S); destruct H9 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Gte z z0) = ZF_BF (ZBF_Gte z z0)) by auto; specialize (H10 _ _ S); destruct H10 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_BF (ZBF_Eq z z0) = ZF_BF (ZBF_Eq z z0)) by auto; specialize (H11 _ _ S); destruct H11 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    exfalso; apply (simp_no_eq_max f z z0 z1); auto.
    exfalso; apply (simp_no_eq_min f z z0 z1); auto.
    assert (S : ZF_BF (ZBF_Neq z z0) = ZF_BF (ZBF_Neq z z0)) by auto; specialize (H12 _ _ S); destruct H12 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_And z1 z2 = ZF_And z1 z2) by auto; specialize (H13 _ _ S); destruct H13 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Or z1 z2 = ZF_Or z1 z2) by auto; specialize (H14 _ _ S); destruct H14 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Imp z1 z2 = ZF_Imp z1 z2) by auto; specialize (H15 _ _ S); destruct H15 as [? [? M]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Not z  = ZF_Not z) by auto; specialize (H16 _ S); destruct H16 as [? M];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Forall v0 q0 z  = ZF_Forall v0 q0 z) by auto; specialize (H17 _ _ _ S); destruct H17 as [? [? [? M]]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.
    assert (S : ZF_Exists v0 q0 z  = ZF_Exists v0 q0 z) by auto; specialize (H18 _ _ _ S); destruct H18 as [? [? [? M]]];
    rewrite MM in M; rewrite SS in M; rewrite M in H5; discriminate H5.

    (* exists rest part *)

    destruct (judge (simplify f)); intros; split; split; intros;
    repeat match goal with
             | [|- satisfied (ZF_BF (ZBF_Const VTrue))] => rewrite satisfied_unfold; simpl; trivial
             | [|- dissatisfied (ZF_BF (ZBF_Const VFalse))] => rewrite dissatisfied_unfold; simpl; trivial
             | [H: dissatisfied (ZF_BF (ZBF_Const VTrue)) |- _] => rewrite dissatisfied_unfold in H; simpl in H; discriminate H
             | [H: satisfied (ZF_BF (ZBF_Const VFalse)) |- _] => rewrite satisfied_unfold in H; simpl in H; discriminate H
             | [H: satisfied (ZF_BF (ZBF_Const VError)) |- _] => rewrite satisfied_unfold in H; simpl in H; discriminate H
             | [H: dissatisfied (ZF_BF (ZBF_Const VError)) |- _] => rewrite dissatisfied_unfold in H; simpl in H; discriminate H
             | [H: _ /\ _ |- _] => destruct H
           end.

    rewrite satisfied_unfold; split;
    [exists N.Const0; assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [SAT _]]; apply SAT;
            destruct (simp_subst_the_same f q N.Const0 v) as [M _] |
            intros; left; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]]; apply SAT;
            destruct (simp_subst_the_same f q x v) as [M _]]; specialize (M _ e); rewrite MM in M; rewrite M;
    rewrite satisfied_unfold; simpl; trivial.

    rewrite dissatisfied_unfold in H0; specialize (H0 N.Const0); assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [_ DST]];
    apply DST in H0; destruct (simp_subst_the_same f q N.Const0 v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite dissatisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite satisfied_unfold in H0; destruct H0 as [[x ?] ?]; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]];
    apply SAT in H0; destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite satisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite dissatisfied_unfold; intros. assertSS f x q v n. destruct (IHn _ S) as [_ [_ DST]]; apply DST.
    destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M; rewrite M.
    rewrite dissatisfied_unfold; simpl; trivial.

    rewrite satisfied_unfold in H0; destruct H0 as [[x ?] ?]; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]];
    apply SAT in H0; destruct (simp_subst_the_same f q x v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite satisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite dissatisfied_unfold in H0; specialize (H0 N.Const0); assertSS f N.Const0 q v n; destruct (IHn _ S) as [_ [_ DST]];
    apply DST in H0; destruct (simp_subst_the_same f q N.Const0 v) as [M _]; specialize (M _ e); rewrite MM in M;
    rewrite M in H0; rewrite dissatisfied_unfold in H0; simpl in H0; discriminate H0.

    rewrite satisfied_unfold in H0; rewrite satisfied_unfold; destruct H0 as [[x ?] ?]; split.
    exists x; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]]; rewrite SS; apply SAT, H0.
    intros; specialize (H4 x0); assertSS f x0 q v n; destruct (IHn _ S) as [_ [SAT DST]]; rewrite SS;
    destruct H4; [left; apply SAT | right; apply DST]; apply H4.

    rewrite satisfied_unfold in H0; rewrite satisfied_unfold; destruct H0 as [[x ?] ?]; split.
    exists x; assertSS f x q v n; destruct (IHn _ S) as [_ [SAT _]]; rewrite SS in H0; apply SAT, H0.
    intros; specialize (H4 x0); assertSS f x0 q v n; destruct (IHn _ S) as [_ [SAT DST]]; rewrite SS in H4;
    destruct H4; [left; apply SAT | right; apply DST]; apply H4.

    rewrite dissatisfied_unfold in H0; rewrite dissatisfied_unfold; intros; specialize (H0 x); assertSS f x q v n;
    destruct (IHn _ S) as [_ [_ DST]]; rewrite DST in H0; rewrite <- SS in H0; apply H0.

    rewrite dissatisfied_unfold in H0; rewrite dissatisfied_unfold; intros; specialize (H0 x); assertSS f x q v n;
    destruct (IHn _ S) as [_ [_ DST]]; rewrite DST; rewrite <- SS; apply H0.
  Qed.

End SimplifyProof.
