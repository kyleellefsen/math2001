## Logic
All capital letters A, B, C in this section are of type `Prop`. 

### Moving $\uparrow$ the proof tree
If your proof state is below the horizontal line, you can move up by using the tactic written on the right of the line.

---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$\Gamma $}
   \RL{ exact}
   \LL{$\uparrow$}
   \UIC{$ \Gamma, a: A ⊢ A$}
\end{prooftree}
$$
```lean
example (A : Prop) (a : A) : A := by
	exact a
```

$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$ \Gamma, h: A \to B ⊢ A$}
   \RL{ apply h}
   \LL{$\uparrow$}
   \UIC{$ \Gamma, h: A \to B ⊢ B$}
\end{prooftree}
$$
```lean
example (A B: Prop) (h: A → B) (a : A) : B := by
  apply h 
  exact a
```

---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$ \Gamma, a: A ⊢ B$}
   \RL{ intro a}
   \LL{$\uparrow$}
   \UIC{$ \Gamma ⊢ A \to B $}
\end{prooftree}
$$

```lean
example (A B : Prop) (b : B): A → B := by
  intro a
  exact b
```
---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$ \Gamma ⊢ A$}
   \RL{ left}
   \LL{$\uparrow$}
   \UIC{$ \Gamma ⊢ A ∨ B$}
\end{prooftree}
$$
```lean
example (A B : Prop) : A → A ∨ B := by
  intro a
  left
  exact a
```
---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$ \Gamma ⊢ B$}
   \RL{ right}
   \LL{$\uparrow$}
   \UIC{$ \Gamma ⊢ A ∨ B$}
\end{prooftree}
$$

```lean
example (A B : Prop) : B → A ∨ B := by
  intro b
  right
  exact
```
---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$\Gamma, a: A ⊢ $}
   \AXC{} \noLine
   \UIC{$\Gamma, b: B ⊢ $}
   \RL{ cases h with | inl a => ... | inr b=> ...}
   \LL{$\uparrow$}
   \LL{$\uparrow$}
   \BIC{$\Gamma, h: A \lor B ⊢ $}
\end{prooftree}
$$
```lean
example (A B : Prop) : A ∨ B → B ∨ A := by 
  intro h
  cases h with
  | inl a => 
    right 
    exact a
  | inr b =>
    left
    exact b
```

---
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$\Gamma ⊢ A$}
   \AXC{} \noLine
   \UIC{$\Gamma ⊢ B $}
   \RL{ constructor}
   \LL{$\uparrow$}
   \BIC{$\Gamma ⊢A \land B  $}
\end{prooftree}
$$
```lean
example (A B : Prop) (a: A) (b: B) : A ∧ B := by
  constructor 
  exact a  -- left case
  exact b  -- right case 
```
### Moving $\downarrow$ the proof tree
$$
\begin{prooftree}
   \AXC{} \noLine
   \UIC{$ \Gamma, h: A \land B ⊢ $}
   \RL{ obtain ⟨a, b⟩ := h}
   \LL{$\downarrow$}
   \UIC{$\Gamma, a: A, b: B ⊢ $}
\end{prooftree}
$$
```lean
example (A B : Prop) (h: A ∧ B) : A := by
  obtain ⟨a, b⟩ := h
  exact a
```
---