# Proofs for formal-conjectures

Lean 4 proofs of statements from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
That repository collects statements and asks for proofs longer than 25–50 lines to be hosted
elsewhere and linked with the `@[formal_proof]` attribute. This repository hosts such proofs.

Each file imports the statement from formal-conjectures at a fixed commit (see `lakefile.toml`)
and ends with a check that the proved theorem has exactly the type of the repository statement:

```lean
example : type_of% Erdos588.erdos_588.variants.trivial_upper := trivial_upper
```

| File | Statement in formal-conjectures | Result |
|---|---|---|
| [`FcProofs/Erdos588.lean`](FcProofs/Erdos588.lean) | `Erdos588.erdos_588.variants.trivial_upper` | $f_k(n) \cdot k(k-1) \leq n(n-1)$ for $k \geq 2$ |
| [`FcProofs/Erdos670.lean`](FcProofs/Erdos670.lean) | `Erdos670.erdos_670.variants.choose_two` | $n \neq 2$ points with separated distances have diameter $\geq \binom{n}{2}$ |
| [`FcProofs/Erdos935.lean`](FcProofs/Erdos935.lean) | `Erdos935.erdos_935.parts.ii`, `Erdos935.erdos_935.variants.ell_two`, `Erdos935.erdos_935.variants.mahler` | $\limsup_n Q_2(n(n+1)\cdots(n+\ell))/n^2$ is infinite for $\ell \geq 2$ and at least $1$ for $\ell \geq 1$ |

`#print axioms` for every proved theorem gives only `propext`, `Classical.choice` and
`Quot.sound`.

## Build

```bash
lake exe cache get
lake build
```

## License

MIT, see [LICENSE](LICENSE). The imported statements are from formal-conjectures (Apache 2.0).

AI-usage disclosure: Claude (Anthropic) was used as assistant.
