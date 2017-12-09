{-
  This program is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.
  
  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.
  
  You should have received a copy of the GNU General Public License
  along with this program.  If not, see <http://www.gnu.org/licenses/>.
-}


In this module some System F programs are encoded as an EDSL in haskell

> {-# LANGUAGE RankNTypes,
>              UnicodeSyntax,
>              ScopedTypeVariables,
>              ExplicitForAll #-}

> module SystemF where
> import Prelude hiding (and)

Let the type of booleans be:

> type 𝔹 = ∀ x. x → x → x

we define the values:

> tru ∷ 𝔹
> tru = \t f → t

> fls ∷ 𝔹
> fls = \t f → f

We define some fuctions, note that free variables on types
can be actually be closed by a forall quantifier on the left

> if₂ ∷ 𝔹 → a → a → a
> if₂ = \cond thn els -> cond thn els

> neg ∷ 𝔹 → 𝔹
> neg = \b -> b fls tru

> and ∷ 𝔹 → 𝔹 → 𝔹
> and = \l r → l r fls

We can define more functions this way with no difficulty.
Let's go to more interesting stuff.

Naturals:


> type ℕ = ∀ x. (x → x) → x → x

> z ∷ ℕ
> z = \f x → x

> s ∷ ℕ → ℕ
> s = \n f x → f (n f x)  

< n3 = s $ s $ s $ z

With this representation we cannot print
values as they are represented, since they are functions.
There are many possible
solutions to this. For instane we can program a function of type
\mathbb{N} \to {\tt Int } (Haskell's Int type) and then print,
or directly apply SystemF values to a print function.

< n3 (\n -> n+1) 0 -- reduces to 3!

Let's define:

\begin{itemize}

\item Addition:

> (⊕) ∷ ℕ → ℕ → ℕ
> (⊕) = \m n f x → m f (n f x) 

\item Multiplication

> (⊛) ∷ ℕ → ℕ → ℕ
> (⊛) = \m n f x → m (n f) x 

\end{itemize}

Some constants

> n0  = z
> n1  = s $ z
> n2  = s $ n1
> n3  = s $ n2
> n5  = n2 ⊕ n3
> n10 = n5 ⊛ n2

Lists:

> type List a = ∀x. x → (a → x → x) → x

> nil ∷ List a
> nil = \n c → n

> cons ∷ ∀ a. a → List a → List a

> cons = \a l n c → c a (l n c)  
