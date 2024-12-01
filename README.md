# VerIso: Verifiable Isolation Guarantees for Database Transactions

## Description

VerIso is the first mechanized framework for formally specifying database designs and systematically verifying a variety of isolation guarantees for all their behaviors. This means there are no restrictions on the number of transactions or clients and servers and when you successfully verify a protocol using this framework, you get a rigorous correctness guarantee. The framework also helps with identifying isolation bugs in database designs.

The supported isolation guarantees are:
* RA (Read Atomicity)
* UA (Update Atomicity)
* TCC (Transactional Causal Consistency)
* PC (Prefix Consistency)
* SI (Snapshot Isolation)
* PSI (Parallel SI)
* SER (Serializability)
* SSER (Strict SER)

## Isolation guarantees proofs and falsifications

* Modeling and verification of the Strict Two-Phase Locking protocol can be found in [S2PL.thy](VerIso/S2PL.thy) and [S2PL_Proof.thy](VerIso/S2PL_Proof.thy).

* Modeling and falsification of TAPIR are available in [Tapir.thy](VerIso/Tapir.thy) and [Tapir_Falsification.thy](VerIso/Tapir_Falsification.thy). We have additionally performed black-box testing on TAPIR's implementation using IsoVista, which can be found in [TapirBBTest](https://github.com/lucamul/TapirCorrectnessTest) submodule.
  
* To load all theories, including the simple database example from the paper and each case studies' proof/falsification, see the [Run.thy](Run.thy) theory.

In addition, our modeling and verification of our novel Eiger_PORT protocol can be found in [EPplus repository](https://github.com/ShabnamRad/EPplus/) (submodule in [VerIso](VerIso/)).


## Usage
- To load the Isabelle theories, install the latest version of Isabelle/HOL at https://isabelle.in.tum.de/index.html.
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
