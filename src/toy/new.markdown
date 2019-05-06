Okay, this thought isn't totally well formed yet so I'm kinda using you to form
it. I've been trying to make this concrete for a couple weeks but I haven't
really needed to confront it head on.

Right, so the problem I'm having with implementing `preservation` is that I
don't have a handle on what happens inside of functions such as
`typeCheckInterp`.  In simple examples like we did last night we have the entire
definition of the things we are trying to prove at compile time (i.e., we aren't
being passed any variables in, and Idris can just run the functions in question
on the inputs and directly check equality):

```
i  = MkInterp [] [ConstOp (I32 0)]
i' = MkInterp [I32 0] []

-- Here Idris just computes everything directly, so no abstract reasoning
-- was needed or applied; this approach does not generalize
step_i_eq_i' : step i = Right i'   
step_i_eq_i' = Refl
```

However, we will want to work with values that we don't know anything about
(i.e., if all we know is that `Step i i'`).

If I have something of type `OneStep i i'` I essentially have a proof that `step
i = Right i'`. If in addition I know that `HasType i t`, I essentially have a
proof that `typeCheckInterp i = Just t`. However, all of this has happened
behind opaque function calls such as `step` and `typeCheckInterp`, and we cannot
use the computations made by those functions (i.e., the pattern matching) to
help us in our next proof.

A fix to this would be to make our types have a 'certificate of computation',
telling us _how_ the it was proved that, say, this interpreter had this type.
For instance, here is part of a definition of `HasType`:

```
-- We may need to lift the map definition up to the type level as well
data TypedStack : List Val -> List Tp -> Type where
    ST : vs -> TypedStack vs (map valToTp vs)

data HasType : Interp -> InterpTp -> Type where
    HTConst32 : i@(MkInterp vs (Const32 :: es)) 
             -> TypedStack vs ts
             -> HasType i (T32 :: ts)
    HTAdd32   : i@(MkInterp vs (BinOp IAdd32 :: es))
             -> TypedStack vs (T32 :: T32 :: ts)
             -> HasType i (T32 :: Ts)
    -- etc
```

Additionally, I think we would want to rewrite our `OneStep` type:

```
data OneStep : Interp -> Interp -> Type where
    StepConst32 : i@(MkInterp vs (Const32 x :: es))
               -> OneStep i (MkInterp (x :: vs) es)
    HTAdd32 : i@(MkInterp (I32 x :: I32 y :: vs) (BinOp IAdd32 :: es)
           -> OneStep i (MkInterp (I32 (x + y) :: vs) es)
```

Then to prove preservation we would do something like this

```
preservation : OneStep i i' -> HasType i t -> HasType i' t
preservation (Step i i' prf) (HasTp i t tp_i_t) = ?rhs
```

