module DataflowSafety

import Data.List.Quantifiers
import Data.List
import Data.Vect

--------------------------------------------------------------------------------
-- Stuff to skip
--------------------------------------------------------------------------------

fromDec : Dec a -> Maybe a
fromDec (Yes a) = Just a
fromDec (No _)  = Nothing

append : {a : Type}
      -> (xs : List a)
      -> (ys : List a)
      -> (zs : List a ** xs ++ ys = zs)
append [] ys = (ys ** Refl)
append (x :: xs) ys with (append xs ys)
  | (zs ** pf) = (x :: zs ** rewrite pf in Refl)

interface HasList1 (f : List a -> Type) where
  ixList1 : f as -> (bs : List a ** as = bs)

--------------------------------------------------------------------------------
-- Typed Datalog datatypes and some operations
--------------------------------------------------------------------------------

Var : Type
Var = String

vars1 : HasList1 f => f vs -> (vs' : List Var ** vs = vs')
vars1 = ixList1

data DataflowMode = MPlus | MDontCare

data Predicate : {arity : Nat} -> Vect arity DataflowMode -> Type where
  MkPredicate : {arity : Nat}
             -> {modes : Vect arity DataflowMode}
             -> (name : String)
             -> Predicate modes

data Term = TVar String | TLit String

vars : {len : Nat} -> Vect len Term -> List Var
vars []               = []
vars ((TVar x) :: xs) = x :: vars xs
vars ((TLit x) :: xs) = vars xs

modedVars : {len : Nat} -> Vect len DataflowMode -> Vect len Term -> List Var
modedVars []                []               = []
modedVars (MDontCare :: ms) (_        :: ts) =        modedVars ms ts
modedVars (_         :: ms) (TLit _   :: ts) =        modedVars ms ts
modedVars (MPlus     :: ms) (TVar var :: ts) = var :: modedVars ms ts

modedVarsL : {len : Nat}
          -> (modes : Vect len DataflowMode)
          -> (terms : Vect len Term)
          -> (mVars : List Var ** mVars = modedVars modes terms)
modedVarsL []                []               = ([] ** Refl)
modedVarsL (MDontCare :: ms) (term     :: ts) = modedVarsL ms ts
modedVarsL (MPlus     :: ms) ((TLit _) :: ts) = modedVarsL ms ts
modedVarsL (MPlus     :: ms) ((TVar v) :: ts) =
  let (vs ** prf) = modedVarsL ms ts
  in (v :: vs ** rewrite sym prf in Refl)

data Atom : List Var -> List Var -> Type where
  MkAtom : {arity : Nat}
        -> {modes : Vect arity DataflowMode}
        -> (predicate : Predicate modes)
        -> (terms : Vect arity Term)
        -> Atom (modedVars modes terms) (vars terms)

HasList1 (Atom modedVars) where
  ixList1 (MkAtom _ terms) = go terms
  where
    go : (terms : Vect arity Term) -> (vs : List Var ** vars terms = vs)
    go [] = ([] ** Refl)
    go (t :: ts) with (go ts)
      go ((TVar v) :: _)| (vs ** pf) = (v :: vs ** rewrite pf in Refl)
      go ((TLit _) :: _)| (vs ** pf) = (vs ** pf)

Head : List Var -> Type
Head vars = Atom Nil vars

Subseteq : {a : Type} -> List a -> List a -> Type
Subseteq xs ys = All (\x => Elem x ys) xs

data Body : List Var -> Type where
  EmptyBody : Body Nil
  SnocBody  : {bodyVars : List Var}
           -> {atomVars : List Var}
           -> Body bodyVars
           -> Atom modedVars atomVars
           -> Subseteq modedVars bodyVars
           -> Body (atomVars ++ bodyVars)

HasList1 Body where
  ixList1 EmptyBody = ([] ** Refl)
  ixList1 (SnocBody {bodyVars = bVars} {atomVars = aVars} _ _ _) =
    append aVars bVars

data Clause : Type where
  MkClause : {headVars : List Var}
          -> {bodyVars : List Var}
          -> Head headVars
          -> Body bodyVars
          -- | Range restriction
          -> Subseteq headVars bodyVars
          -> Clause

Program : Type
Program = List Clause

--------------------------------------------------------------------------------
-- Untyped versions of the above and smart constructors
--------------------------------------------------------------------------------

data SomeAtom = SA (Atom modedVars vars)
data SomeHead = SH (Head vars)
data SomeBody = SB (Body vars)

decNoModedVars : (modes : Vect n DataflowMode)
              -> (terms : Vect n Term)
              -> Dec (modedVars modes terms = [])
decNoModedVars []                []         = Yes Refl
decNoModedVars (MDontCare :: xs) (_ :: ys)  = decNoModedVars xs ys
decNoModedVars (MPlus :: xs) (TLit _ :: ys) = decNoModedVars xs ys
decNoModedVars (MPlus :: xs) (TVar v :: ys) = No uninhabited

decSubseteq : {a : Type}
           -> DecEq a
           => (xs : List a) -> (ys : List a) -> Dec (Subseteq xs ys)
decSubseteq xs ys = all (\x => isElem x ys) xs

mkHead : SomeAtom -> Maybe SomeHead
mkHead (SA atom) = SH <$> (go atom)
  where
  go : Atom modedVars vars -> Maybe (Head vars)
  go (MkAtom (MkPredicate {modes = modes} name) terms)
    with (decNoModedVars modes terms)
    | Yes prf = rewrite sym prf in Just (MkAtom (MkPredicate name) terms)
    | No _    = Nothing

mkBody : List SomeAtom -> Maybe SomeBody
mkBody [] = Just (SB EmptyBody)
mkBody (SA atom :: atoms) = do
    SB body <- mkBody atoms
    SB <$> go atom body
  where
  go : Atom _ atomVars -> Body bodyVars -> Maybe (Body (atomVars ++ bodyVars))
  go atom body = do
    let MkAtom (MkPredicate {modes = modes} name) terms = atom
    let (mVars ** prf1) = modedVarsL modes terms
    let (bVars ** Refl) = vars1 body
    wellModednessPrf <- fromDec $ decSubseteq mVars bVars
    pure (SnocBody body atom (rewrite sym prf1 in wellModednessPrf))

mkClause : SomeAtom -> List SomeAtom -> Maybe Clause
mkClause someAtom someAtoms = do
    SH head <- mkHead someAtom
    SB body <- mkBody $ reverse someAtoms
    let (headVars ** Refl) = vars1 head
    let (bodyVars ** Refl) = vars1 body
    prf <- fromDec $ decSubseteq headVars bodyVars
    pure $ MkClause head body prf

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

p : Predicate [ MPlus, MDontCare ]
p = MkPredicate "p"

easy : Predicate [ MDontCare ]
easy = MkPredicate "easy"

someEasy : SomeAtom
someEasy = SA $ MkAtom easy [ TVar "X" ]

groundP : Atom [] [ "X" ]
groundP = MkAtom p [ TLit "Mistral", TVar "X" ]

someGroundP : SomeAtom
someGroundP = SA groundP

modedP : Atom [ "X" ] [ "X", "Y" ]
modedP = MkAtom p [ TVar "X", TVar "Y" ]

someModedP : SomeAtom
someModedP = SA modedP

tests : List ((SomeAtom, List SomeAtom), Bool)
tests =
  [ ((someEasy, [ someEasy ]) , True)
  , ((someEasy, [ someModedP ]), False)
  , ((someEasy, [ someGroundP ]), True)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ ]), False)
  , ((someEasy, [ someEasy, someModedP ]), True)
  , ((someEasy, [ someModedP, someEasy ]), False)
  , ((someEasy, [ someEasy, someGroundP, someModedP ]), True)
  ]

main : IO ()
main = for_ (zip tests (take (length tests) [1..])) displayTestCase
  where
  displayTestCase : (((SomeAtom, List SomeAtom), Bool), Int) -> IO ()
  displayTestCase ((testCase, expectation), ix) =
    if isJust (uncurry mkClause testCase) == expectation
      then putStrLn "Test passed."
      else putStrLn $ "Test #" <+> show ix <+> " failed."
