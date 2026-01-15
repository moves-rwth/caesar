---
title: Verification of Almost-Sure Termination with Distributed Algorithms at POPL 2026
authors: phisch
tags: [publications]
---

The paper [_"Verifying Almost-Sure Termination for Randomized Distributed Algorithms"_](https://doi.org/10.1145/3776691) was presented at the [ACM SIGPLAN Symposium on Principles of Programming Languages (POPL) 2026](https://popl26.sigplan.org/) held in Rennes, France.
The authors are Constantin Enea (LIX, CNRS, Ecole Polytechnique), Rupak Majumdar (MPI-SWS), Harshit Jitendra Motwani (MPI-SWS), V.R. Sathiyanarayana (MPI-SWS).

The paper presents a verification technique for liveness properties of randomized distributed algorithms.
It introduces a proof rule for fair almost-sure termination of distributed systems, combining martingale-based arguments for probabilistic termination with reasoning about weak fairness.
The proof rules are implemented in Caesar and were used to verify termination of randomized asynchronous consensus protocols, including Ben-Or’s protocol and graded binary consensus, under both crash and Byzantine faults.

<!-- truncate -->

The excellent presentation by Sathiya is available on YouTube:

<iframe
  width="560"
  height="315"
  src="https://www.youtube-nocookie.com/embed/MaoVQWD8z5Q?si=09q5hbsBYVRBbMhu&start=2880"
  title="YouTube video player"
  frameborder="0"
  allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share"
  referrerpolicy="strict-origin-when-cross-origin"
  allowfullscreen>
</iframe>

<details>
    <summary>Full abstract (as provided by the authors)</summary>

    We present a technique for the verification of liveness properties of randomized distributed algorithms. Our technique gives SMT-based proofs for many common consensus algorithms, both for crash faults and for Byzantine faults. It is based on a sound proof rule for fair almost-sure termination of distributed systems that combines martingale-based techniques for almost-sure termination with reasoning about weak fairness.

    Our proof rule is able to handle parametrized protocols where the state grows unboundedly and every variant function is unbounded. These protocols were out of scope for previous approaches, which either relied on bounded variant functions or on reductions to (non-probabilistic) fairness.

    We have implemented our proof rules on top of Caesar, a program verifier for probabilistic programs. We use our proof rule to give SMT-based proofs for termination properties of randomized asynchronous consensus protocols, including Ben-Or's protocol and graded binary consensus, for both crash and Byzantine faults. These protocols have notoriously difficult proofs of termination but fall within the scope of our proof rule.
</details>

We will make more detailed information available on how to use these techniques with Caesar on this website in the future.
