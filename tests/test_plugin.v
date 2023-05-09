Add LoadPath "~/M1/Stage/coq-waterproof/theories" as Waterproof.
Add ML Path "~/M1/Stage/coq-waterproof/src".

Print Waterproof.

Goal forall P: Prop, P -> P.
Proof.
  hello.
  tactid P.