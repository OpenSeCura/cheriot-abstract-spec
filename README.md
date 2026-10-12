# cheriot-abstract-spec

A Rocq model intended to describe the CHERIoT execution model as the CHERIoT RTOS presents it to user code: a multithreaded machine whose threads run in CHERI compartments, where a thread switch, a cross-compartment call or return, and the entry of an exception handler are single steps rather than sequences of instructions, each with a semantics supplied per instruction under a well-formedness condition.  The development states what a well-formed configuration of compartments and threads is, defines the step relation of the machine, states the contracts of the RTOS switcher separately from that relation (they are specified, not proved, and not connected to the step relation), and proves one top-level theorem: on same-domain executions, no thread gains reach over capabilities it could not already reach at the start.

## What is modeled

- **Capabilities** as an abstract record: a cursor and the list of addresses in bounds, permissions, a sealing state (unsealed, sealed with a key, or one of the sentry kinds), the sealing and unsealing keys it holds, the labels of capabilities it may store and under which it may itself be stored (local or non-local), and the permissions and labels a capability loaded through it keeps.  The concrete CHERIoT encoding is not used inside the model; `CHERIoTValidation` maps the compressed permission formats and object types of the ISA onto the abstract record, by a function that is intended to follow the ISA and is not proved to.
- **Memory** as bytes with a tag per capability slot, read and written through capabilities, with the conditions under which a store of a capability, a tag removal, or a data write is valid.
- **Reachability**: the capabilities and addresses a set of capabilities can reach by loading, restricting, sealing and unsealing, which is the quantity the theorem bounds.
- **Threads and the machine**: a register file, PCC, MEPCC and MTCC, a trusted stack of frames and a liveness status per thread; a current thread index, a memory and an interrupt status for the machine.
- **Instructions** of four kinds, each carrying its own semantics as a function and a proof that the function is well formed: general instructions, compartment calls through a sentry, compartment returns, and exception entries.  The well-formedness condition of a general instruction includes that it does not increase the set of reachable capabilities; the development does not provide a concrete instruction set and does not prove that condition for one.
- **Steps and events**: a thread step fetches, decodes and executes one instruction, or traps when the fetch is not permitted; a machine step is a step of the current thread or a switch of the current thread, and each records an event in a trace.
- **Configurations**: compartments with code and data capabilities, import and export tables and sealing capabilities, threads with their initial stacks and starting compartments, the initial memory, and the switcher with its entry points and sealing key; what makes such a configuration well formed and a machine a valid initial state of it.
- **The switcher's contracts**: pre- and postconditions of the switcher's entry points (exception entry and return, compartment call and return, stack unwinding) in terms of the registers and the memory at the time of entry, written as an abstraction of the switcher in CHERIoT RTOS's `entry.S`.  They are specified, not proved, and nothing in the model connects them to the step relation; see "Status".

Outside the model: memory-mapped I/O and shared objects, the RTOS scheduler and liveness, and anything below the ISA.  The sources mark the first two with `TODO`.

## Building

The development is built with Rocq 9.3 and needs nothing beyond the Rocq standard library (`Stdlib`).

```sh
make          # generates Makefile.coq from _CoqProject and builds the five files
make clean    # removes the build products and Makefile.coq
```

The build takes a few seconds and produces five `.vo` files under `src/`, in the logical namespace `cheriot` (`-Q src cheriot`).  To check that the main theorem rests on nothing but the kernel:

```
Require Import cheriot.Properties.
Print Assumptions ThreadIsolatedMonotonicity.ThreadIsolatedMonotonicity.
```

prints `Closed under the global context`.  Rocq 9.1.0 does not build the current sources: its `rocq makefile` rejects the `--no-rocq-package-warning` option the `Makefile` passes, and it has no `Abbreviation` command, which the sources use.  Rocq 9.2 was not tried.

## The theories

Five files, in dependency order.  `Tactics.v` and `Utils.v` are support; `Spec.v` is the model; `SpecLemmas.v` and `Properties.v` are what is proved and specified about it.

### `Tactics.v`

Proof automation used throughout: tactics for inverting and simplifying equalities (`simplify_eq`, `simplify_tuples`, `inv`), for case analysis on matches, products and disjunctions (`simpl_match`, `case_match`, `destruct_products`, `destruct_or`), for splitting conjunctions and learning hypotheses (`split_and`, `learn_hyp`, `consider`), and the closers `done`, `by` and `fast_done`; the `MARK` inductive that `mark` uses to record progress in a proof.  One lemma, `simple_tuple_inversion`.

### `Utils.v`

General definitions and lemmas, grouped by subject.

- `Combinators`: `always`, the inductive-invariant shape of the main theorem (an invariant is established on the initial state, preserved by every step, and implies the property), and `until`.
- `EqSet`, `Subset`, `Result`: set equality and inclusion of lists, and a result type.
- `Option`, `Forall`, `Subset`, `ListUpdate`: lemmas on options, on `Forall` and `Forall2`, on list inclusion, and on updating a list at an index; `listSumToInl` and `seqInBounds`.
- `Separation`: `Disjoint`, `Pairwise` and `Separated`, the disjointness predicates the isolation hypotheses use.

### `Spec.v`

The model.  `ISA_params` (the capability size and the number of registers), `Perm` (the permission vocabulary), and `MachineTypeParams` (the byte and key types) are parameters of everything that follows.  The `Machine` section then defines, in order (its inner sections `CapStep`, `Transitivity`, `UpdMem`, `ValidState` and `WithContext` are named where they fall):

- the address types, `Label`, `Sentry`, the `Cap` record and the memory types: the `CapEncodeDecode` interface between bytes and capabilities, and the read and write operations on memory and tags;
- `CapHelpers`: sealing, cursor and bounds updates, the sentry and sealed-data tests, and `attenuate`, the load-side attenuation of permissions and labels;
- `CurrMemory`: for a fixed memory, the one-step relations between capabilities (`CapStep`: `RestrictUnsealed`, `RestrictSealed`, `Restrict`, `LoadCap`, `Seal`, `Unseal`), their transitive closure (`Transitivity`: `ReachableCap`, `ReachableAddr`, `ReachableCaps`), and the conditions a memory update must meet (`UpdMem`: `ValidMemCapUpdate`, `ValidMemTagRemoval`, `ValidMemDataUpdate`, `ValidMemUpdate`);
- the inner `Machine` section: register files, trusted-stack frames and stacks, user and system thread states, `Thread` and `Machine`, with `capsOfThread` and the other projections of the capabilities a thread holds; `ReachableMemSame` and `UpdatedMemSame`; `ValidState`: `ValidRf`;
- the instruction kinds, each with its semantic function type and its well-formedness condition: `NormalInst` (`FuncNormal`, `WfNormalInst`), `SystemInst` (`FuncSystem`, `WfSystemInst`), `GeneralInstruction` (`WfGeneralInst`, which combines the two according to the system permission), `CallSentryInst`, `RetSentryInst` and `ExnInst`; then `Inst`, the events (`SameThreadEvent`, `Event`) and `Trace`;
- `FetchDecodeExecute`: the fetch function and its condition `FetchAddrsOk`, the decoder, and, in `WithContext`, the trap state, `threadStepFunction` and `ThreadStep`; then `SameThreadStep` and `MachineStep`.

`CHERIoTValidation` closes the file: the compressed permission formats (`CompressedPerm`), a concrete capability record (`cheriot_cap`), the decompression of permissions (`decompress_perm`), and `mk_abstract_cap`, which builds an abstract `Cap` from a concrete one, including the object-type encoding of sentries and sealed capabilities.

### `SpecLemmas.v`

Lemmas about the model, under the same parameters (one `WithContext` section binds them).  `ReachabilityDefs` defines the reachable read, write and execute addresses, `RWAddressesDisjoint`, `ReachableCapSubset` and `WriteReadDisjoint`; `CapStepLemmas` relates `attenuate` and `Restrict` and proves `Restrict` reflexive and transitive; `ReachableCapLemmas` and `MemUpdateLemmas` show how reachability behaves under capability steps and under valid memory updates; `SeparationLemmas` show that a thread's reach is unchanged by updates to memory disjoint from it; `CapsOf`, `WFInstructionLemmas` (what a well-formed general instruction or call preserves) and `Step` (what a same-thread step leaves unchanged) are used by the properties.

### `Properties.v`

Four modules, each binding its parameters in a `WithContext` section (the `WithConfig`, `WithSwitcherParams`, `Proofs` and `Utils` sections inside them fix a configuration, the switcher's register conventions, or hold proofs and helpers).

- `Configuration` (specified and proved): the export and import tables, compartments, threads, the switcher and `Config`; the footprints; `WFCompartment`, `WFSwitcher` and `WFConfig`; `ValidInitialState` with its trusted-stack and thread conditions; and `GlobalInvariant`, the part of initial validity that every `MachineStep` preserves.  Nine lemmas, ending in `GlobalInvariantStep`.
- `SwitcherProperty` (**specified only, no proofs**): the contracts of the switcher's entry points, written as an abstraction of the switcher in CHERIoT RTOS's `sdk/core/switcher/entry.S`: `UnwindingStack`, `ExceptionHandler` (stackful and stackless), `ExceptionReturn`, `CompartmentCall` and `CompartmentReturn`, each as an invariant, a precondition and a postcondition over the register file, the thread's stack and the trusted stack.  Some clauses are commented out with a `TODO`, one of them noted as not true of the current switcher; the module is a draft specification, not connected to the step relation, and nothing checks it against the implementation.
- `CompartmentIsolationValidation` (proved): on the initial state only, compartments that are not connected on the audit graph (`ReachableCompartment`) share no addresses, sentries or switcher-sealed capabilities; seventeen lemmas, ending in `InitialPropertyHolds`.
- `ThreadIsolatedMonotonicity` (proved): the main theorem, below; seven lemmas and the theorem.

## The main theorem

```
Theorem ThreadIsolatedMonotonicity :
  forall config initial_machine,
  WFConfig config ->
  ValidInitialMachine config initial_machine ->
  Combinators.always MachineStep (PThreadIsolatedMonotonicity initial_machine) (initial_machine, []).
```

Take a well-formed configuration and a valid initial machine whose threads start with pairwise-disjoint read/write reach.  In every state reachable by the step relation whose trace so far contains only same-domain events (thread switches and general instructions, as opposed to compartment calls, compartment returns and exceptions), each thread can reach only capabilities that were reachable from its initial state.  Thread isolation is a hypothesis on the initial machine and a conjunct of the proof's invariant, not a conclusion of the theorem.

What it does not say: `PThreadIsolatedMonotonicity` is an implication from the whole trace being same-domain, so after the first compartment call, compartment return or exception the property holds vacuously, and the theorem claims nothing about such events or about what follows them.  The switcher's contracts, which govern those events, are specified in `SwitcherProperty` and not proved.  Per-instruction monotonicity is assumed, not proved: it is part of `WfGeneralInst`, the proof obligation every general instruction carries, and the theorem lifts it to whole executions.  The theorem is parametric in the capability encoding, the fetch function and the decoder, and says nothing about any particular one.

## Status

- No `Admitted` proofs and no axioms; `Print Assumptions` on the main theorem is closed under the global context.
- The events and traces of `Spec.v` are marked work in progress in the sources; `SwitcherProperty` is a specification without proofs.
- The sources carry `TODO` markers, most of them in `Properties.v`.  Several mark known gaps rather than cleanup: memory-mapped I/O and shared objects are not in the configuration; a well-formedness condition on the initial stack is still to be fixed; a block of the exception-return postcondition is commented out, one clause of it noted as not true of the current switcher; liveness is not treated.  Read them before relying on a clause near them.

## Related repositories

- [`OpenSeCura/cheriot`](https://github.com/OpenSeCura/cheriot): the CHERIoT ISA specification, formal verification and implementation in Guru.  This repository is parametric in the instruction set and does not use that specification.
- [`OpenSeCura/cheriot-program-logic`](https://github.com/OpenSeCura/cheriot-program-logic): a work-in-progress ISA-level program logic for a subset of CHERIoT instructions, with an example on part of the switcher's context-restore path.
- [`Cherified/Guru`](https://github.com/Cherified/Guru): the Rocq framework for hardware specification and verification in which `cheriot` is written.
- [`CHERIoT-Platform/cheriot-sail`](https://github.com/CHERIoT-Platform/cheriot-sail): the CHERIoT ISA specification, in Sail, with the architecture document; `CHERIoTValidation` is intended to follow its permission and object-type encodings, and is not proved to.
- [`CHERIoT-Platform/cheriot-rtos`](https://github.com/CHERIoT-Platform/cheriot-rtos): the RTOS whose switcher (`sdk/core/switcher/entry.S`) the contracts in `SwitcherProperty` abstract, and whose issue [#559](https://github.com/CHERIoT-Platform/cheriot-rtos/issues/559) one of them cites.

## References

What the model describes:

- CHERIoT architecture specification: [cheriot-architecture.pdf](https://cheriot.org/cheriot-sail/cheriot-architecture.pdf) (capabilities, permissions, sentries and sealing as encoded by `CHERIoTValidation`).
- CHERIoT RTOS: [`docs/architecture.md`](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/docs/architecture.md) and the switcher, [`sdk/core/switcher/entry.S`](https://github.com/CHERIoT-Platform/cheriot-rtos/blob/main/sdk/core/switcher/entry.S) (the entry points and the trusted stack that `SwitcherProperty` specifies).
- *CHERIoT: Complete Memory Safety for Embedded Devices*, MICRO 2023, and the Microsoft Research technical report [*CHERIoT: Rethinking security for low-cost embedded systems*](https://www.microsoft.com/en-us/research/publication/cheriot-rethinking-security-for-low-cost-embedded-systems) (2023).

Related work:

- Nienhuis et al., *Rigorous engineering for hardware security: Formal modelling and proof in the CHERI design and implementation process*, IEEE S&P 2020, and Bauereiss et al., *Verified Security for the Morello Capability-enhanced Prototype Arm Architecture*, ESOP 2022: reachable-capability monotonicity proved over ISA models, the property whose thread-level form is proved here.
- [Griotte](https://arxiv.org/abs/2609.01110): a verified compartmentalization switcher for a CHERI machine.
- [CHERIoT-Ibex observational correctness](https://arxiv.org/abs/2502.04738) and [VeriCHERI](https://arxiv.org/abs/2407.18679): verification of CHERIoT implementations at the RTL level.
- Murali Vijayaraghavan, *Rigorous Hardware Software Codesign for Secure Compartmentalization on Embedded Devices*, [CHERITech25](https://cheri-alliance.org/wp-content/uploads/2025/11/3.3-Murali-Vijayaraghavan-Rigorous-Hardware-Software-Codesign-for-Secure-Compartmentalization-on-Embedded-Devices-CHERITech25.pdf) (November 2025): the framing of this model, with the RTOS specification as constraints on atomic operations.

## License

Apache License 2.0; see `LICENSE` and the headers of the sources.
