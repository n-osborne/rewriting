Record ARS : Type :=
  mkARS
    { elt : Type ;
      red : elt -> elt -> Prop
    }.

Inductive TransitiveClosure (A: ARS): elt A -> elt A -> Prop :=
  | tc_head : forall {x y}, red A x y -> TransitiveClosure A x y
  | tc_cons : forall {x y z}, TransitiveClosure A x y -> red A x y -> TransitiveClosure A x z.

Definition ReflexiveTransitiveClosure (A: ARS)(x y : elt A) : Prop :=
  x = y \/ TransitiveClosure A x y.

Definition SymmetricClosure (A: ARS)(x y: elt A) : Prop :=
  red A x y \/ red A y x.

Inductive TransitiveSymmetricClosure (A: ARS): elt A -> elt A -> Prop :=
| tsc_head: forall {x y}, SymmetricClosure A x y -> TransitiveSymmetricClosure A x y
| tsc_cons: forall {x y z}, TransitiveSymmetricClosure A x y -> SymmetricClosure A y z -> TransitiveSymmetricClosure A x z.

Definition ReflexiveTransitiveSymmetricClosure (A: ARS)(x y: elt A) : Prop :=
  x = y \/ TransitiveSymmetricClosure A x y.
