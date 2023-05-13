From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

(* Map functions and definitions taken from the Maps.v file of
  Software Foundations volume 2. *)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
Admitted.
Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
Admitted.
Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
Admitted.
Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
Admitted.
Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.
Proof.
Admitted.
Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
Admitted.
Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).
Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.
Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.
Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.
Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.
Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.
Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.
Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.
Lemma includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.




(* Begin: Cypher *)

(* Start with importing the necessary libraries *)
From Coq Require Import Sets.Ensembles.
From Coq Require Import Lists.ListSet.




(* The infinite sets (K, N, R) that graph relies on*)
Inductive id_key : Type := 
  | ID_Key (n: nat).

Inductive id_node : Type := 
  | ID_Node (n: nat).

Inductive id_rel : Type := 
  | ID_Rel (n: nat).

(* Now, the labels and relationship types sets *)
Inductive id_label : Type :=
  | ID_Label (s: string).

Inductive id_reltype : Type :=
  | ID_Reltype (s: string).


(* Decidability lemmas *)
Definition eq_dec : forall x y : nat, {x = y} + {x <> y}. decide equality. Defined.
Definition eq_dec_id_key: forall x y : id_key, {x = y} + {x <> y}. decide equality. apply eq_dec. Defined.
Definition eq_dec_id_node: forall x y : id_node, {x = y} + {x <> y}. decide equality. apply eq_dec. Defined.
Definition eq_dec_id_rel: forall x y : id_rel, {x = y} + {x <> y}. decide equality. apply eq_dec. Defined.
Definition eq_dec_id_label: forall x y : id_label, {x = y} + {x <> y}. decide equality. apply string_dec. Defined.
Definition eq_dec_id_reltype: forall x y : id_reltype, {x = y} + {x <> y}. decide equality. apply string_dec. Defined.


(* Define paths *)
Inductive path : Type :=
  | Singular (n : id_node)
  | Connect (n : id_node) (r : id_rel) (p : path)
.

(* A couple of useful functions with paths *)
Fixpoint concat_paths_with_rel (p1:path) (r:id_rel) (p2:path) : path :=
  match p1 with
  | Singular n => Connect n r p2 
  | Connect n r1 p => Connect n r1 (concat_paths_with_rel p r p2)
  end
.

Fixpoint concat_paths_formal (p1:path)(p2:path) : path :=
  match p1 with
  | Singular n => p2
  | Connect n r1 p => Connect n r1 (concat_paths_formal p p2)
  end
.

Fixpoint len_by_node (p1: path) : nat :=
  match p1 with
  | Singular _ => 1
  | Connect _ _ p => 1 + (len_by_node p)
  end
.

Fixpoint get_nth_node (p1: path) (n: nat) : option id_node :=
  match p1 with
  | Singular node =>
    (match n with
      | 1 => Some node
      | _ => None
     end)
  | Connect node _ p =>
    (match n with
      | 1 => Some node
      | _ => get_nth_node p (n-1)
     end)
  end
.

Definition get_first_node (p1: path) : id_node :=
  match p1 with
  | Singular node => node
  | Connect node _ _ => node
  end
.

Fixpoint get_nth_rel (p1: path) (n: nat) : option id_rel :=
  match p1 with
  | Singular node => None
  | Connect _ rel p =>
    (match n with
      | 1 => Some rel
      | _ => get_nth_rel p (n-1)
     end)
  end
.

Fixpoint paths_concattable (p1: path) (p2: path) : Prop :=
  match p1 with
  | Singular n1 =>
    (match p2 with
      | Singular n2 => n1=n2
      | Connect n2 _ _ => n1=n2
    end
    )
  | Connect _ _ p => paths_concattable p p2
  end
.

Theorem len_node_implies_not_none_node : forall p m,
  len_by_node p >= m -> exists n, get_nth_node p m = Some n.
Proof. Admitted.



(* Now, values. Currently incomplete *)
Inductive value : Type :=
  | V_ID_Node (n : id_node)
  | V_ID_Rel (n : id_rel)
  | V_Int (x: nat) (* not integer *)
  | V_Str (s: string)
  | V_Bool (b : bool)
  | V_Null
  | V_List (l : list value)
  | V_Map (* incomplete *)
  | V_Path (p : path)
  | V_Error
.




(* Graph definition! A tuple *)
Definition graph := 
  (set id_node *     (* Set N: the nodes of G *)
   set id_rel *       (* Set R: the relationships of G *)
   (id_rel -> option id_node) *   (* src: R->N, maps rel to its source node *)
   (id_rel -> option id_node) *   (* tgt: R->N, maps rel to its target node *)
   (*ι: (N∪R) X K -> V., split into two: *)
   (id_node -> id_key -> option value) *
   (id_rel -> id_key -> option value) *
   (id_node -> (set id_label)) * (* λ Issue: id_labels have to come from defined L *)
   (id_rel -> option id_reltype) (* τ *)
)%type.

(* This module has the labels and relationship types draw from given sets.
Future work may need this.*)
Module SpecificLT.
Definition graph (L: Set) (T: Set)  := 
  (set id_node *     (* Set N: the nodes of G *)
   set id_rel *       (* Set R: the relationships of G *)
   (id_rel -> id_node) *   (* src: R->N, maps rel to its source node *)
   (id_rel -> id_node) *   (* tgt: R->N, maps rel to its target node *)
   (*ι: (N∪R) X K -> V., split into two: *)
   (id_node -> id_key -> value) *
   (id_rel -> id_key -> value) *
   (id_node -> (set L)) *
   (id_rel -> T)
)%type.
End SpecificLT.



(* Validity proposition of a graph *)
Definition valid (g: graph) : Prop :=
    match g with
      | (N, R, src, tgt, iN, iR, ld, tau) => 
        (forall x, set_In x R -> exists v, src x = Some v) /\
        (forall x, set_In x R -> exists v, tgt x = Some v) /\
        (forall v, exists x, src x = Some v -> set_In v N) /\
        (forall v, exists x, tgt x = Some v -> set_In v N)
        (* ι has finite nonnull outputs - incomplete *)
    end
.


(* Simple functions to extract parts of graphs *)
Definition get_N (g : graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => N
  end
.
Definition get_src (g : graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => src
  end
.
Definition get_tgt (g : graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => tgt
  end
.

Definition get_lambda (g : graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => ld
  end
.
Definition get_iota_node (g : graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => iN
  end
.
Definition get_tau (g: graph) :=
  match g with
  | (N, R, src, tgt, iN, iR, ld, tau) => tau
  end
.

(* Paths can have direction, and validity of paths is based on that *)
Inductive direction : Type :=
  | left_to_right
  | right_to_left
  | undirected
.

(* Validity of path on a graph *)
Fixpoint valid_path (g: graph) (p: path) (d:direction) : Prop :=
  match p with
  | Singular ni => true = set_mem eq_dec_id_node ni (get_N g)
  | Connect ni r p1 => true =(set_mem eq_dec_id_node ni (get_N g)) ->
    ( match p1 with
      (* Does not currently account for direction *)
      | Singular nj => (get_src g) r = Some ni /\ (get_tgt g) r = Some nj
      | Connect nj _ _ => (get_src g) r = Some ni /\ (get_tgt g) r = Some nj 
      end
    ) -> valid_path g p1 d
  end
.




(* Begin: expression AST data structure *)
Definition var_name:Type := string.
Definition prop_list:Type := nat. (* This is a placeholder *)

Inductive expr:Type := 
  (* Values/variables *)
  | Value (v: value)
  | Name (a: var_name)
  | Func (f: value -> value) (exl: list expr) (* incomplete: f should take len(exl) values *)

  (* Maps *)
  | EmptyMap
  | SelectMap (e1: expr) (k: id_key)
  | MakeMap (pl: prop_list)

  (* Lists *)
  | EmptyList
  | MakeList (ex1: list expr)
  | INList (e: expr) (l: expr)

  (* List selection *)
  | ListSingle (l: expr) (i: expr)
  | ListFrom (l: expr) (i: expr)
  | ListTo (l: expr) (i: expr)
  | ListFromTo (l: expr) (i: expr) (j: expr)

  (* Strings *)
  | STARTS (esearch: expr) (equer: expr)
  | ENDS (esearch: expr) (equer: expr)
  | CONTAINS (esearch: expr) (equer: expr)

  (* Logic *)
  | OR (e1: expr) (e2: expr)
  | AND (e1: expr) (e2: expr)
  | XOR (e1: expr) (e2: expr)
  | NOT (e1: expr)
  | ISNULL (e1: expr)
  | NOTNULL (e1: expr)

  (* Comparison *)
  | Lt (e1: expr) (e2: expr)
  | Le (e1: expr) (e2: expr)
  | Gt (e1: expr) (e2: expr)
  | Ge (e1: expr) (e2: expr)
  | Eq (e1: expr) (e2: expr)
  | Nq (e1: expr) (e2: expr)
.



(* A record is the Cypher name for an environment *)
Definition record := partial_map value.

(* Begin : evaluation of expressions *)
Fixpoint eval_expr (g:graph) (u:record) (e:expr)  : value :=
  match e with
  (* Values/variables*)
  | Value v => v
  | Name a => (match u a with | None => V_Error | Some v => v end)
  | Func f e => V_Bool false (* incomplete *)
  (* Maps *)
  | EmptyMap => V_Map (* incomplete *)
  (* Lists *)
  | EmptyList => V_List ((nil: list value))
  | MakeList el => V_List (map (eval_expr g u) el)
  | INList e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | v, V_List l => V_Error (* incomplete (In v l) doesn't work - decidability*)
                  | _,_ => V_Error
                  end)

  (* List selection *)
  (* Incomplete *)

  | STARTS e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Str s1, V_Str s2 => V_Bool (prefix s1 s2)
                  | _,_ => V_Error
                end)
  | ENDS e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Str s1, V_Str s2 => V_Bool (prefix s1 s2) (* incomplete, need other func *)
                  | _,_ => V_Error
                end)
  | CONTAINS e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Str s1, V_Str s2 => V_Bool (prefix s1 s2) (* incomplete, need other func *)
                  | _,_ => V_Error
                end)

  (* Logic *)
  | OR e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Bool b1, V_Bool b2 => V_Bool (b1 || b2)
                  | _,_ => V_Error
                end)
  | AND e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Bool b1, V_Bool b2 => V_Bool (b1 && b2)
                  | _,_ => V_Error
                end)
  | XOR e1 e2 => (match (eval_expr g u e1 ), (eval_expr g u e2) with
                  | V_Bool b1, V_Bool b2 => V_Bool ((b1 && (negb b2)) || ((negb b1) && b2))
                  | _,_ => V_Error
                end)
  | NOT e1 => (match (eval_expr g u e1) with
                  | V_Bool b1 => V_Bool (negb b1)
                  | _ => V_Error
                end)
  | ISNULL e1 => (match (eval_expr g u e1)with
                  | V_Null => V_Bool true
                  | _ => V_Bool false
                end)
  | NOTNULL e1 => (match (eval_expr g u e1)with
                  | V_Null => V_Bool false
                  | _ => V_Bool true
                end)
  | _ => V_Error
  end
.


(* Define patterns! *)


(* (a, L, P) *)
Definition node_pattern :=
  (
  option expr *
  set id_label *
  (id_key -> option value) (* Should be expression but simple steps *)
)%type.

Definition rel_pattern :=
  (
  direction *
  option id_node *
  set id_reltype *
  (id_key -> option value) *
  (option nat * option nat) (* Fix, this can also be nil option nat*)
)%type.

Inductive path_pattern : Type :=
  | Sing (x : node_pattern)
  | Conn (x : node_pattern) (r : rel_pattern) (p : path_pattern)
.



(* Satisfaction of patterns definition *)
Inductive path_pattern_match : (path * graph * (record)) -> path_pattern -> Prop :=

  (* Single node match *)
  | Node_match : forall n G u a L P, 
    a = None \/ (exists e, Some e = a /\ (eval_expr G u e) = V_ID_Node n) -> 
    (forall l, set_In l L -> set_In l ((get_lambda G) n)) ->
    (* P k needs to be evaluated in context *)
    (forall k, exists v, P k = Some v -> 
      get_iota_node G n k = Some v) ->
    path_pattern_match (Singular n, G, u) (Sing ((a, L, P):node_pattern))
  (* Length 0 path *)
  | Zero_match : forall n p G u χ d a T P π,
    (* Missing: evaluating a *)
    (* Valid path *)
    (paths_concattable (Singular n) p) ->
    (* Node match *)
    (path_pattern_match (Singular n, G, u) (Sing χ)) ->
    (path_pattern_match (p, G, u) π) ->
    path_pattern_match 
      ((concat_paths_formal (Singular n) p), G, u)
      (Conn (χ) ((d, a, T, P, (Some 0, Some 0)):rel_pattern) (π))
  (* Rigid length path *)
  | Non_zero_rigid_match: forall p1 p G u χ d a T P m π,
    (* Missing: evaluating a *)
    (* Valid path *)
    (paths_concattable p1 p) ->
    (* Valid length path *)
    len_by_node p1 = m+1 ->
    (* Node match and rest of path matches *)
    ((path_pattern_match (Singular (get_first_node p1), G, u) (Sing χ))) ->
    (path_pattern_match (p, G, u) π) -> 
    (* All relationships in p1 are subset of T *)
    (forall r, exists n, Some r = get_nth_rel p1 n ->
        exists tt, (get_tau G) r = Some tt -> true = set_mem eq_dec_id_reltype tt T) ->
    (* Not doing, evaluate the k's so [ι(r, k) = P(k)] for k's where P(k) defined *)
    (* This is the values and evaluating expressions *)
    (True -> True) ->
    (* Ensure valid path *)
    (valid_path G p1 d) -> (* currently not perfect because direction isn't accounted for *)
    path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m, Some m)):rel_pattern) (π))
  (* Variable length (fixed endpoints) match *)
  | Variable_match: forall p1 p G u χ d a T P m n π,
    (exists m', m <= m' -> m' <= n -> path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m', Some m')):rel_pattern) (π))) ->
    path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m, Some n)):rel_pattern) (π))
  (* Only right is fixed *)
  | Variable_match_left_null: forall p1 p G u χ d a T P n π,
    (exists m', m' <= n -> path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m', Some m')):rel_pattern) (π))) ->
    path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (None, Some n)):rel_pattern) (π))
  (* Only left is fixed *)
  | Variable_match_right_null: forall p1 p G u χ d a T P m π,
    (exists m', m <= m' -> path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m', Some m')):rel_pattern) (π))) ->
    path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m, None)):rel_pattern) (π))
  (* Both unfixed *)
  | Variable_match_both_null: forall p1 p G u χ d a T P π,
    (exists m', path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (Some m', Some m')):rel_pattern) (π))) ->
    path_pattern_match 
      ((concat_paths_formal p1 p), G, u)
      (Conn (χ) ((d, a, T, P, (None, None)):rel_pattern) (π))

.



(* Begin query AST! *)

Inductive ret:Type :=
  | Star
  | aggexpr (* incomplete *)
.

Inductive pattern_tuple :=
  | OnePatTup (p: path_pattern)
  | ConPatTup (p: path_pattern) (t: pattern_tuple)
.

Inductive clause:Type :=
  | MATCH (pt: pattern_tuple)
  | MATCHWHERE (pt: pattern_tuple) (e: expr)
  | WITH (r: ret)
  | WITHWHERE (r: ret) (e: expr)
  | UNWIND (e: expr) (a: var_name)
.

Inductive query':Type :=
  | RETURN (r: ret)
  | CQ (c: clause) (q: query')
.

Inductive query:Type :=
  | Simple (q: query')
  | UNION (q1: query')
.


Definition table:Type := list (record).


(* Place holders - to be done by implementation *)
Definition free (p: path_pattern): set var_name := nil:(set var_name).
Definition domain (r: record) : set var_name := nil:(set var_name).
Definition record_dot (r1 r2: record) : record := empty:record.
Definition match_p (pi:path_pattern) (G: graph) (r:record) : table :=
  (nil:table)
  (* Should "return" a list of all ui that can be added *)
  (* Specifically u*u', although this is slightly off semantics *)
  (* Forall ui, (p, G, u*u') |= pi -> add to list *)
  (* For future implementations *)
.


Definition match_pattern_tuple (pt: pattern_tuple) (G: graph) (r: record) : table :=
  (nil:table)
  (* Rely on match_p *)
.


(* Type testing - to keep for future use *)
Definition type_testing (pt:pattern_tuple) (g: graph) (t: table) :=
  @fold_left (list record) (list record) (@rev_append (record)) (map (match_pattern_tuple pt g) t) nil:table
.

Check type_testing.


(* Now, evaluating queries *)

(* Evaluating return clauses - incomplete *)
Definition eval_ret (g: graph) (r: ret) (t: table) : table :=
  match r with
  | Star => t 
  | aggexpr => nil:table (* incomplete *)
  end
.

(* Incomplete eval of clauses *)
Definition eval_clause (g: graph) (c: clause) (t: table) : table :=
  match c with
  | MATCH pt =>  
      (* For all records r in table, get t' = match_pattern_tuple(pt, g, r) (which are tables).
          append all of them together to get one master table *)
      @fold_left (list record) (list record) (@rev_append (record)) (map (match_pattern_tuple pt g) t) nil:table
  | MATCHWHERE pt e => nil:table
  | WITH r => nil:table
  | WITHWHERE r e => nil:table
  | UNWIND e a => nil:table
  end
.

(* Relies on eval_clause and eval_ret, but complete *)
Fixpoint eval_query' (g: graph) (q: query') (t: table) : table :=
  match q with 
  | RETURN r => eval_ret g r t
  | CQ cl qr => eval_query' g qr (eval_clause g cl t)
  end
.

Definition eval_query (g: graph) (q: query) (t: table) : table :=
  match q with
  | Simple qr => eval_query' g qr t
  | UNION _ => nil:table (* Incomplete *)
  end
.



(* Sample graph *)
Definition teacher_graph : graph :=
  (
    (* Set N: nodes of G *)
    (
      set_add eq_dec_id_node (ID_Node 1) 
        (set_add eq_dec_id_node (ID_Node 2) 
          (set_add eq_dec_id_node (ID_Node 3) 
            (set_add eq_dec_id_node (ID_Node 4) nil))) 
    ),

    (* Set R: relationships of G *)
    (
      set_add eq_dec_id_rel (ID_Rel 1) 
        (set_add eq_dec_id_rel (ID_Rel 2) 
          (set_add eq_dec_id_rel (ID_Rel 3) nil))
    ),

    (* src: R->N, maps relationship to source node *)
    (fun x:id_rel => if eq_dec_id_rel x (ID_Rel 1) then Some (ID_Node 1) else
                    (if eq_dec_id_rel x (ID_Rel 2) then Some (ID_Node 2) else
                    (if eq_dec_id_rel x (ID_Rel 3) then Some (ID_Node 3) else None))),

    (* tgt: R->N, maps relationship to target node *)
    (fun x:id_rel => if eq_dec_id_rel x (ID_Rel 1) then Some (ID_Node 2) else
                    (if eq_dec_id_rel x (ID_Rel 2) then Some (ID_Node 3) else
                    (if eq_dec_id_rel x (ID_Rel 3) then Some (ID_Node 4) else None))),

    (* Extra information: none for this graph *)
    (fun x:id_node => fun y:id_key => None:option value),
    (fun x:id_rel => fun y:id_key => None:option value),

    (* λ: id_labels for nodes *)
    (fun x:id_node => if eq_dec_id_node x (ID_Node 1) then (set_add eq_dec_id_label (ID_Label "Teacher") nil) else
                     (if eq_dec_id_node x (ID_Node 2) then (set_add eq_dec_id_label (ID_Label "Student") nil) else
                     (if eq_dec_id_node x (ID_Node 3) then (set_add eq_dec_id_label (ID_Label "Teacher") nil) else
                     (if eq_dec_id_node x (ID_Node 3) then (set_add eq_dec_id_label (ID_Label "Teacher") nil) else
                      (nil:set id_label))))),

    (* τ: id_reltype for id_rels *)
    (fun x:id_rel => if eq_dec_id_rel x (ID_Rel 1) then Some (ID_Reltype "KNOWS") else
                    (if eq_dec_id_rel x (ID_Rel 2) then Some (ID_Reltype "KNOWS") else
                    (if eq_dec_id_rel x (ID_Rel 3) then Some (ID_Reltype "KNOWS") else None)))
).


(* Sample query: *)
(* [MATCH (x) -[:KNOWS1..3]-> (y)] *)

Definition sample_path : path_pattern :=
  Conn 
    (* (x) *)
    ((Some (Name (("x"%string):var_name)),(nil: set id_label),(fun y:id_key => None:option value)))
    (* -[:KNOWS1..3]-> *)
    ((left_to_right),(None:option id_node),(set_add eq_dec_id_reltype (ID_Reltype "KNOWS") nil),
      (fun y:id_key => None:option value),(None,Some 2))
    (* (y) *)
    (Sing ((Some (Name (("y"%string):var_name))),(nil: set id_label),(fun y:id_key => None:option value)))
.

Definition sample_query : query :=
             (* MATCH path_pattern            RETURN * *)
  Simple (CQ (MATCH (OnePatTup sample_path)) (RETURN Star)).



(* Simple query of only selecting one node *)
Definition sample_simple : path_pattern :=
  (Sing ((Some (Name (("y"%string):var_name))),(nil: set id_label),(fun y:id_key => None:option value)))
.

Definition sample_simple_query : query :=
  Simple (CQ (MATCH (OnePatTup sample_simple)) (RETURN Star)).

