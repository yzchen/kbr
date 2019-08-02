## Hilbert Axioms

#### Notes :

- `>` : implication, `->`

- `~` : not, `¬`

- `&` : and, `∧`

- `|` : or, `∨`

#### Axioms

1. p -> (q -> p)

    `>p>qp`

2. (p -> (q -> r)) -> ((p -> q) -> (p -> r))

    `>>p>qr>>pq>pr`

3. (~q -> ~p) -> (p -> q)

    `>>~q~p>pq`

4. p -> (~p -> q)

    `>p>~pq`

5. (~p -> p) -> p

    `>>~ppp`

#### Modus Ponens

1. ((p -> q) ∧ p) -> q

    `>&>pqpq`

#### Hilbert L1 Axioms

1. (∀x p) -> p[x/t]

2. (∀x (p -> q)) -> (∀x p -> ∀x q)

3. p -> ∀x p
