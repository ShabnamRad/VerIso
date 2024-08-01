# VerIso: Verifiable Isolation Guarantees for Database Transactions

## Description

VerIso is the first mechanized framework for formally specifying database designs and systematically verifying a variety of isolation guarantees for all their behaviors. This means there are no restrictions on the number of transactions or clients and servers and when you successfully verify a protocol using this framework, you get a rigorous correctness guarantee. The framework also helps with identifying isolation bugs in database designs.

The supported isolation guarantees are:
* RA (Read Atomicity)
* UA (Update Atomicity)
* TCCv (Transactional Causal Consistency with convergence)
* PC (Prefix Consistency)
* SI (Snapshot Isolation)
* PSI (Parallel SI)
* SER (Serializability)
* SSER (Strict SER)

## Isolation guarantees proofs and falsifications

* Verification of the Two-Phase Locking protocol satisfying strict serializability can be found in [S2PL_Proof.thy](VerIso/S2PL_Proof.thy).

* Verification of our novel Eiger_PORT protocol can be found in [EP+_Proof.thy](VerIso/EP+_Proof.thy). The reduction and refinement proofs are available at [EP+_Reduction.thy](VerIso/EP+_Reduction.thy) and [EP+_Refinement_Proof.thy](VerIso/EP+_Refinement_Proof.thy) respectively.

* Modelling and falsification of TAPIR are available in [Tapir.thy](VerIso/Tapir.thy) and [Tapir_Falsification.thy](VerIso/Tapir_Falsification.thy).
  
* To load all theories, including each case studies' proof/falsification, see the [Run.thy](Run.thy) theory.

## Improving isolation guarantees and performance evaluation
Our Eiger-PORT+ protocol improves the upper bound of isolation guarantees achievable by performance-optimal read-only transactions in the presence of transactional writes from the previvously conjectured TCC (Transactional Causal Consistency) to TCCv (TCC with convergence). Additionally, Eiger-PORT+ outperforms the state-of-the-art. Evaluation results are available under the [eiger-port-plus_evaluation](https://github.com/lucamul/EIGER-PORT-PLUS) submodule.

## Usage
- To compile the Isabelle theories, install the latest version of Isabelle/HOL at https://isabelle.in.tum.de/index.html.
- Run the [Run.thy](Run.thy) theory in Isabelle. This theory (directly or transitively) imports all theories of our framework and case studies.
- To see the progress on loading theories check Isabelle's "Theories" panel.
- To inspect the proof state, please make sure "Proof state" box is checked in Isabelle's "Output" tab.
  * To only see the lemmas or theorems statement, place the cursor on them and look at Isabelle's Output tab.
  * To see the lemma statement and proof in the original theory where it is proven, Ctrl + Click on its name. (Cmd + Click for mac users)

## Authors
- Shabnam Ghasemirad

- Dr. Christoph Sprenger

- Dr. Si Liu

- Luca Multazzu

- Prof. David Basin
