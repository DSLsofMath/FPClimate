% -*-Latex-*-
%if False

\begin{code}

{-# OPTIONS --without-K #-}

module Monadic_part1 where

open import Data.Nat using (zero; suc; ℕ; _+_)
open import Data.Float using (Float)
open import Data.Vec using (Vec; []; _∷_; map; head; tail; _++_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
                      renaming ([_] to ηList; map to fmapList; concat to μList)
import Agda.Primitive  -- for Levels
open Agda.Primitive using (Level; lsuc; _⊔_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- data _≡_ {A : Set} : A -> A -> Set where
--   refl : {a : A} -> a ≡ a

-- trans : ∀ {A : Set} {x y z : A} -> (x ≡ y) -> (y ≡ z) -> (x ≡ z)
-- trans refl refl = refl

-- cong : ∀ {A B : Set} (f : A -> B) {x y : A} (p : x ≡ y) -> (f x ≡ f y)
-- cong f refl = refl

dom : {A B : Set} -> (A -> B) -> Set
dom {A} f = A

id : {A : Set} -> A -> A
id a = a

infixr 9 _∘_
_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) a = f (g a)

infixr 6 _<=>_
_<=>_ : {A B : Set} -> (A -> B) -> (A -> B) -> Set
f <=> g = (x : dom f) -> f x ≡ g x

_QED : {ℓ : Level} → {A : Set ℓ} → (x : A) → x ≡ x
x QED = refl

infixr 10 _=⟨_⟩=_   -- emacs agda-mode: \langle \rangle

_=⟨_⟩=_ : {ℓ : Level} → {A : Set ℓ} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩= q = trans p q

\end{code}

%endif


\date{Part 1, 2024-04-22}

\begin{frame}
\maketitle
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Where we are}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Where we are}

%
First half (mostly done):
\begin{enumerate}
\item[15] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2010_Vulnerability_Modelling.pdf}{Vulnerability modelling with functional programming and dependent types}
\item[16] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2011_TestingVsProving.pdf}{Testing versus proving in climate impact research}
\item[17] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2012_DepTy_SciComp_978-3-642-41582-1_9.pdf}{Dependently-Typed Programming in Scientific Computing - Examples from Economic Modelling}
\item[18] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2014_Jansson-Patrik-Computational-Theory-of-GSS.pdf}{Towards a Computational Theory of GSS: a Case for Domain-Specific Languages}
\end{enumerate}
%
\pause
%
\hl<2>{Second half (upcoming):}
\begin{enumerate}
\item[19] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2017a_SeqDecProb1.pdf}{\hl<3>{Sequential decision problems, dependent types and generic solutions}}
\item[20] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2017b_contributions-to-a-computational-theory-of-policy-advice-and-avoidability.pdf}{\hl<3>{Contributions to a computational theory of policy advice and avoidability}}
\item[21] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2018_esd-9-525-2018.pdf}{\hl<4->{The impact of uncertainty on optimal emission policies}}
\item[22] \href{https://github.com/DSLsofMath/FPClimate/blob/main/ref/2023_MatterMost_s10666-022-09867-w.pdf}{\hl<4->{Responsibility Under Uncertainty: Which Climate Decisions Matter Most?}}
\end{enumerate}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Plan}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Plan}

\begin{block}{Today:}
  \begin{itemize}
  \item The computational structure of |possible|: Monadic dynamical systems
  \end{itemize}
\end{block}

\pause

\begin{block}{Next week (18 or 19):}
\begin{itemize}
  \item Background: climate science, climate policy under uncertainty
\end{itemize}
\end{block}

\pause

\begin{block}{Week 19 or 20:}
\begin{itemize}
\item Sequential decision problems
\item Bellman's equation, backward induction
\item Verified policy advice in a nutshell
\end{itemize}
\end{block}

\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{The computational structure of |possible|: Monadic dynamical systems}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{The computational structure of |possible|: Monadic dynamical systems}

\begin{itemize}
\vfill
\item<1-> Recap vulnerability theory
\vfill
\item<2-> |State|, |Evolution| and deterministic systems
\vfill
\item<3-> Non-deterministic systems
\vfill
\item<4-> Monadic systems
\end{itemize}
%
\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Recap vulnerability theory}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Recap vulnerability theory}

%format postulate = "\hl<1-2>{postulate}"
\begin{code}
postulate State Evolution V W  :  Set

postulate F                    :  Set -> Set

postulate fmap                 :  {A B : Set} -> (A -> B) -> F A -> F B

postulate possible             :  State -> F Evolution

postulate harm                 :  Evolution -> V

postulate measure              :  F V -> W
\end{code}

\pause

\begin{code}
vulnerability                  :  State -> W

vulnerability                  =  measure ∘ fmap harm ∘ possible
\end{code}

\begin{itemize}
\vfill
\item<3-> The theory is \hl<2->{applied} (instantiated) by defining |State|, |Evolution|, etc.
\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\begin{itemize}
\vfill
\item<1-> Values of type |State| represent the state of a \hl<1>{system}
\vfill
\item<2-> Example 1: a \hl<2>{reduced} climate system as in \href{https://github.com/DSLsofMath/FPClimate/blob/main/extra/Marina Martínez Montero et al. SURFER v1.0: A flexible and simple model linking emissions to sea level rise.pdf}{\hl<2->{SURFER}}
\vfill
\item<3-> Example 2: a simplified \hl<3>{climate}-\hl<3>{economy} system as in \href{https://github.com/DSLsofMath/FPClimate/blob/main/extra/Ikefuji et al. DICE simplified (2019).pdf}{\hl<2->{DICE simplified}}
\vfill
\item<4-> Example 3: a detailed \hl<4>{climate} system like in EMICs,
  GCMs, etc.
\vfill
\item<5-> |possible s : F Evolution| are the \hl<5>{possible} evolutions starting in |s : State|
\vfill
\item<6-> Thus, either |State| or |possible| have to entail some
  representation of both \hl<6>{natural} and \hl<6>{anthropogenic}
  \hl<6>{forcing} on the system, for example global GHG emissions
\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\begin{itemize}
\vfill
\item<1-> Remember that |Evolution| is the type of evolutions or \hl<1>{scenarios}
\vfill
\item<2-> In a \hl<2>{deterministic}, \hl<2>{time} \hl<2>{continuous}
setting, evolutions are \hl<2>{certain}
\vfill
\item<3-> Often, they can be described by differential equations, for example ODE

\begin{equation*}
\dot{x} \ t = f \ (x \ t) = (f \circ x) \ t
\end{equation*}

\vfill
\item<4-> In this case |F = Id| and \hl<4>{the} evolution starting in $(t_0, x_0)$
is obtained by \hl<5-6>{integration}:

\pause\pause\pause\pause

\begin{equation*}
\varphi \ t \ (t_0, x_0)
=
(t_0 + \int_{t_0}^{t_0 + t}\!\!\!\!\!\!\!\!\! d\tau, \ x_0 + \int_{t_0}^{t_0 + t}\!\!\!\!\!\!\!\!\! f \ (x \ \tau) \ d\tau)
=
(t_0 + t, \ x \ (t_0 + t))
\end{equation*}

\end{itemize}

\pause

\begin{exercise}
  \label{exercise4.1}
  Let |x : Real -> Real|. What are the types of $\dot{x}$, $f$, $\varphi$ in the
  expressions above?
\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\vfill
\begin{exercise}
  \label{exercise4.2}
  Which function is $\varphi \ 0$? Which function is $\varphi \ (t_1 + t_2)$?
\end{exercise}

\pause

\begin{itemize}

\vfill

\item<2-> The evolution of time continuous,
  deterministic systems on \hl<2>{time} \hl<2>{discretizations}
  $\hat{t} : \mathbb{R}_{+} \rightarrow \mathbb{N} \rightarrow
  \mathbb{R}_{+}$, \ $\hat{t} \ \Delta t \ k = k * \Delta t$ is
  also described by endo-functions

\begin{equation*}
  \hat{\varphi} \ \Delta t \ k = \varphi \ (\hat{t} \ \Delta t \ k)
\end{equation*}

\pause

\begin{exercise}
  \label{exercise4.3}
  What is the type of $\hat{\varphi} \ \Delta t \ k$?
\end{exercise}

%if False

\begin{code}
postulate phi : Float → Float × Float → Float × Float
postulate t'  : Float → ℕ → Float
phi' : Float → ℕ → Float × Float → Float × Float
phi' Δt k = phi (t' Δt k)
\end{code}

%endif

\item<4-> \dots and also that of time \hl<4>{time} \hl<4>{discrete}
deterministic systems, e.g., given by difference equations

\begin{equation*}
x \ (t + 1) = x \ t + g \ (x \ t, x \ (t + 1))
\end{equation*}

\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\begin{itemize}

\vfill
\item<1-> In general, one can model \hl<1>{deterministic} \hl<1>{systems} as endo-functions

\begin{code}
DetSys    :  Set -> Set

DetSys X  =  X -> X
\end{code}

\vfill
\item<2-> The evolutions of a system is then obtained by \hl<2>{iterating} that system:

\begin{code}
detFlow : {X : Set} -> DetSys X -> ℕ -> DetSys X

detFlow f     zero    =  id

detFlow f  (  suc n)  =  detFlow f n ∘ f
\end{code}

\end{itemize}

\pause\pause

\begin{exercise}
  \label{exercise4.4}
  %format next⁴ = "next^4"
  Let |next : State -> State| and |Evolution = Vec State 5|. Define
  |possible : State -> Evolution| such that |possible s| is the
  trajectory under |next| starting in |s|: |possible s = [s, next s, ..., next⁴ s]|.
\end{exercise}

%if False
\begin{code}
postulate next1 : State -> State
possible1 : State -> Vec State 5
possible1 s = map (\ n -> detFlow next1 n s) (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
\end{code}
%endif

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\vfill
\begin{exercise}
  \label{exercise4.5}
    Encode the mathematical specification

    \quad |Forall (m, n ∈ ℕ) (Forall (f : DetSys X) (Forall (x ∈ X) (detFlow f (m + n) x =
      detFlow f n (detFlow f m x))|

in Agda through a function |detFlowP1|.
\end{exercise}

\pause

\vfill
\begin{exercise}
  \label{exercise4.6}
    Implement (prove) |detFlowP1| by induction on |m|.
\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\begin{itemize}

\vfill

\item<1-> One can compute \hl<1>{the} trajectory obtained by iterating a
system |n| times from an initial state:

%format ∷ = ::
\begin{code}
detTrj : {X : Set} -> DetSys X -> (n : ℕ) -> X -> Vec X (suc n)

detTrj f     zero    x  = x ∷ []

detTrj f  (  suc n)  x  = x ∷ detTrj f n (f x)
\end{code}
\end{itemize}

\pause

\vfill
\begin{exercise}
  \label{exercise4.7}
  |detTrj| fulfills a specification similar to |detFlowP1|. Encode this
  specification in the type of a function |detTrjP1| using only |detTrj|, |detFlow|,
  |tail : Vec X (1 + n) -> Vec X n| and vector concatenation |++|.
\end{exercise}


\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{|State|, |Evolution| and deterministic systems}

\begin{itemize}

\vfill

\item<1-> Perhaps not surprisingly, the last element of the trajectory of length
|1 + n| of |f : DetSys X| starting in |x| is just |detFlow f n x|:

%if False
\begin{code}
last : {A : Set} -> {n : ℕ} -> Vec A (suc n) -> A
last (a ∷ []) = a
last (a ∷ a' ∷ as) = last (a' ∷ as)
\end{code}
%endif

\begin{code}
detFlowTrjP1  :  {X : Set} -> (n : ℕ) -> (f : DetSys X) ->

                 (x : X) -> last (detTrj f n x) ≡ detFlow f n x
detFlowTrjP1 = {!!}
\end{code}

\end{itemize}

\pause

\vfill
\begin{exercise}
  \label{exercise4.8}
  Implement |detFlowTrjP1| using

\begin{code}
lastLemma  :  {A : Set} -> {n : ℕ} ->
              (a : A) -> (as : Vec A (suc n)) -> last (a ∷ as) ≡ last as
lastLemma a (x ∷ as) = refl
\end{code}

%if False
\begin{spec}
lastLemma a as = refl        -- works with 2.6.4.1, 2.6.3
lastLemma a (x ∷ as) = refl  -- works with 2.6.2.2
\end{spec}
%endif

\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}

\begin{itemize}

\vfill
\item<1-> Remember that \hl<1>{uncertainty} can be represented
  \hl<1>{functorially}: |possible : State ->| \hl<1>{|F|} |Evolution|

\vfill
\item<2-> For |F| = \hl<2>{|List|}, we have \hl<2>{non}-\hl<2>{deterministic} uncertainty

\vfill
\item<3-> In this case, for a given initial state one can have \hl<3>{zero}, \hl<3>{one}
  or \hl<3>{more} possible \hl<3>{next} states

\vfill
\item<4-> One can \hl<4>{iterate} non-deterministic systems like deterministic ones

%format >=>List = >=>"_{\!List}"
%format fmapList = fmap"_{List}"
%format ηList = "\eta_{List}"
%format μList = "\mu_{List}"

%if False
\begin{code}
infixr 1 _>=>List_
_>=>List_ : {A B C : Set} -> (A -> List B) -> (B -> List C) -> (A -> List C)
f >=>List g = μList ∘ (fmapList g) ∘ f
\end{code}
%endif

\begin{code}
NonDetSys : Set -> Set

NonDetSys X = X -> List X
\end{code}

\begin{code}
nonDetFlow  :  {X : Set} -> NonDetSys X -> ℕ -> NonDetSys X

nonDetFlow f     zero    =  ηList

nonDetFlow f  (  suc n)  =  f >=>List nonDetFlow f n
\end{code}

\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}

\vfill
\begin{exercise}
  \label{exercise4.9}
  What are the types of |ηList| and |>=>List| in the definition of
  |nonDetFlow|?
\end{exercise}

\pause

\vfill
\begin{exercise}
  \label{exercise4.10}
    Define |>=>List| in terms of |fmapList| and |μList| with

  \begin{spec}
    fmapList  :  {A B : Set} -> (A -> B) -> List A -> List B
    μList     :  {A : Set} -> List (List A) -> List A
  \end{spec}

\end{exercise}

\pause

\vfill
%format [_] = [ "\un{}" ]
\begin{exercise}
  \label{exercise4.11}
  Verify that, for arbitrary types |A| and |B|, |ηList = [_]| and |fmapList = map| fulfill

%format ηListNatTrans = ηList NatTrans
\begin{spec}
(f : A -> B) -> (a : A) -> fmapList f (ηList a) ≡ ηList (f a)
\end{spec}

%if False
\begin{code}
ηListNatTrans  :  {A B : Set} -> (f : A -> B) -> (a : A) -> fmapList f (ηList a) ≡ ηList (f a)
ηListNatTrans f a = refl
\end{code}
%endif
\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}

\begin{itemize}

\vfill
\item<1-> With \hl<1>{|fmapList|}, \hl<1>{|ηList|} and
  \hl<1>{|>=>List|}, one can also compute all the possible trajectories

%format ∷_ = ∷"\un"
\begin{code}
nonDetTrj : {X : Set} -> NonDetSys X -> (n : ℕ) -> X -> List (Vec X (suc n))

nonDetTrj f   zero    x  =  fmapList (x ∷_) (ηList [])

nonDetTrj f ( suc n)  x  =  fmapList (x ∷_) ((f >=>List (nonDetTrj f n)) x)
\end{code}

\end{itemize}

\pause

\vfill
\begin{exercise}
  \label{exercise4.12}
  Compute |nonDetFlow rw n zero| and |nonDetTrj rw n zero| for |n = 0,1,2| for the random walk

\begin{code}
rw : ℕ -> List ℕ

rw    zero    =  zero ∷ suc zero ∷ []

rw (  suc m)  =  m ∷ suc m ∷ suc (suc m) ∷ []
\end{code}

\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}

\begin{itemize}

\vfill
\item<1-> Every \hl<1>{deterministic} system can be \hl<1>{represented} by a
  \hl<1>{non-deterministic} one:

\begin{code}
detToNonDet : {X : Set} -> DetSys X -> NonDetSys X

detToNonDet f = ηList ∘ f
\end{code}

\end{itemize}

\pause

\vfill
\begin{exercise}
  \label{exercise4.13}
  Show that

%format Det≡NonDet = Det"\!\!\equiv\!\!"NonDet
\begin{code}
Det≡NonDet  :  {X : Set} -> (f : DetSys X) -> (n : ℕ) -> (x : X) ->

               ηList (detFlow f n x) ≡ nonDetFlow (detToNonDet f) n x
Det≡NonDet = {!!}
\end{code}

by induction on |n| and using |ηListNatTrans| and

\begin{code}
postulate triangleLeftList : {A : Set} -> (as : List A) -> μList (ηList as) ≡ as
\end{code}

\end{exercise}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Non-deterministic systems}

\begin{itemize}

\vfill
\item<1-> Perhaps surprisingly, the opposite is also true

%if False
\begin{code}
infixr 1 _>>=List_
_>>=List_ : {A B : Set} -> List A -> (A -> List B) -> List B
as >>=List f = μList (fmapList f as)
\end{code}
%endif

\begin{code}
nonDetToDet : {X : Set} -> NonDetSys X -> DetSys (List X)

nonDetToDet f = μList ∘ (fmapList f)
\end{code}

\vfill
\item<2-> But the \hl<2>{state} of the resulting deterministic system is now \hl<2>{much} \hl<2>{bigger}!

\vfill
%format >>=List = >>="_{List}"
\item<3-> The function |\ xs -> \ f -> μList ∘ (fmapList f xs)| is usually
denoted by the infix \hl<3>{|>>=List|}

\begin{spec}
nonDetToDet f xs = xs >>=List f
\end{spec}

\vfill
\item<4-> Again, one has a representation theorem

%format NonDet≡Det = NonDet"\!\!\equiv\!\!"Det
\begin{code}
NonDet≡Det  :  {X : Set} -> (f : NonDetSys X) -> (n : ℕ) -> (xs : List X) ->

               nonDetToDet (nonDetFlow f n) xs ≡ detFlow (nonDetToDet f) n xs
\end{code}

%if False
\begin{code}
module ListMonadLaws where
  variable A B : Set
  MapEtaList : (f : A -> B) -> (a : A) -> Set
  MapEtaList f a  =  fmapList f (ηList a) ≡ ηList (f a)
  TriangleLeftList : (as : List A) -> Set
  TriangleLeftList as = μList (ηList as) ≡ as
  TriangleRightList : (as : List A) -> Set
  TriangleRightList as = (μList ∘ fmapList ηList) as ≡ as

  postulate law1 : ∀ (f : A -> B) -> (a : A) -> MapEtaList f a
  postulate law2 : ∀ (as : List A) -> TriangleRightList as
--  postulate  : ∀ as -> TriangleLeftList as  -- already postulated as triangleLeftList
NonDet≡Det f zero     xs =
  nonDetToDet ηList xs                       =⟨ refl ⟩=
  (μList ∘ fmapList ηList) xs                 =⟨ ListMonadLaws.law2 xs ⟩=
  id xs                                      QED
NonDet≡Det f (suc n)  xs =
  nonDetToDet (f >=>List nonDetFlow f n) xs           =⟨ {!!} ⟩=  -- To be continued
  (detFlow (nonDetToDet f) n ∘ nonDetToDet f) xs      QED
\end{code}
%endif

\end{itemize}

\vfill
\end{frame}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{frame}{Monadic systems}
\end{frame}

