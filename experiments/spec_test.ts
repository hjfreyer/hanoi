import {
    MachineSpec, TranscriptEntry, SpecBuilder,
    build, read, write, concurrent, choice, loop, complement, prefix, sequence,
    transition, isCompleted, checkTranscript, parseTranscript,
    getPossibleTransitions, isSubtype
} from "./spec";

const BorrowSpec : SpecBuilder = sequence(
    read(["borrow"]),
    write(["value"]),
    read(["restore"]),
);

const BorrowableSpec : MachineSpec = build(loop(build(BorrowSpec)));

const Copyable = build(loop(build(sequence(read(["copy"]), write(["value"])))));

function pairSpec(left : MachineSpec, right: MachineSpec): SpecBuilder {
    return concurrent({ left, right });
}

function comparator(inner : MachineSpec): SpecBuilder {
    return sequence(
        read(["get"]),
        pairSpec(build(complement(inner)), build(complement(inner))),
        write(["return"]),
    );
}

function pairComparator(left: MachineSpec, right: MachineSpec) {
    return sequence(
        read(["get"]),
        concurrent({
            left : build(complement(build(pairSpec(left, right)))),
            right : build(complement(build(pairSpec(left, right)))),
            leftCmp: build(complement(build(comparator(left)))),
            rightCmp: build(complement(build(comparator(right)))),
        }),
        write(["return"]),
    );
}

const pairBorrowableCopyable = pairComparator(BorrowableSpec, Copyable);

describe("sequence", () => {
    it("returns done for empty sequence", () => {
        expect(build(sequence())).toEqual({ kind: "done" });
    });

    it("creates nested MachineSpec for sequence of parts", () => {
        expect(build(sequence(
            read(["a"]),
            write(["b"])
        ))).toEqual({
            kind: "read",
            channel: ["a"],
            then: {
                kind: "write",
                channel: ["b"],
                then: { kind: "done" }
            }
        });
    });
});

describe("checkTranscript", () => {
    it("matches done with empty transcript", () => {
        expect(checkTranscript(build(sequence()), parseTranscript(``))).toBe(true);
    });

    it("does not match done with non-empty transcript", () => {
        expect(checkTranscript(build(sequence()), parseTranscript(`
            < a
        `))).toBe(false);
    });

    it("matches read with correct single entry", () => {
        expect(checkTranscript(build(sequence(read(["a", "b"]))), parseTranscript(`
            < a.b
        `))).toBe(true);
    });

    it("does not match read with wrong kind", () => {
        expect(checkTranscript(build(sequence(read(["a"]))), parseTranscript(`
            > a
        `))).toBe(false);
    });

    it("does not match read with wrong channel path", () => {
        expect(checkTranscript(build(sequence(read(["a", "b"]))), parseTranscript(`
            < a.c
        `))).toBe(false);
    });

    it("does not match read with different channel length", () => {
        expect(checkTranscript(build(sequence(read(["a"]))), parseTranscript(`
            < a.b
        `))).toBe(false);
    });

    it("does not match if transcript has multiple entries but spec ends with done", () => {
        expect(checkTranscript(
            build(sequence(read(["a"]))),
            parseTranscript(`
                < a
                < a
            `)
        )).toBe(false);
    });

    it("matches a multi-step sequence", () => {
        const spec = build(sequence(
            read(["a"]),
            write(["b"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a
            > b
        `))).toBe(true);
    });

    it("does not match multi-step sequence with incorrect entry", () => {
        const spec = build(sequence(
            read(["a"]),
            write(["b"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a
            < b
        `))).toBe(false);
    });
});

describe("checkTranscript with concurrent", () => {
    it("matches concurrent specs with interleaved entries", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        // interleaved 1
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
        `))).toBe(true);

        // interleaved 2
        expect(checkTranscript(spec, parseTranscript(`
            > right.bar
            < left.foo
        `))).toBe(true);
    });

    it("does not match concurrent spec if one machine is not completed", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
        `))).toBe(false);
    });

    it("fails when passing data to a completed machine", () => {
        const spec = build(concurrent({
            left: build(read(["foo"])),
            right: build(write(["bar"]))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
            < left.foo
        `))).toBe(false);
    });

    it("matches nested concurrent specs", () => {
        const spec = build(concurrent({
            outer: build(concurrent({
                inner: build(read(["foo"]))
            }))
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < outer.inner.foo
        `))).toBe(true);
    });
});

describe("checkTranscript with choice", () => {
    it("matches choice branches", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            err: build(read(["msg"]))
        }));
        // branch 1
        expect(checkTranscript(spec, parseTranscript(`
            < data
        `))).toBe(true);

        // branch 2
        expect(checkTranscript(spec, parseTranscript(`
            < msg
        `))).toBe(true);

        // invalid branch
        expect(checkTranscript(spec, parseTranscript(`
            < other
        `))).toBe(false);
    });

    it("is completed if at least one branch is completed", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(""))).toBe(true);
    });

    it("can still take a different branch even if one branch is completed", () => {
        const spec = build(choice({
            ok: build(read(["data"])),
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < data
        `))).toBe(true);
    });

    it("fails if attempting to pass data to a completed choice branch", () => {
        const spec = build(choice({
            exit: { kind: "done" }
        }));
        expect(checkTranscript(spec, parseTranscript(`
            < anything
        `))).toBe(false);
    });
});

describe("checkTranscript with loop", () => {
    it("matches a loop with 0 iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(``))).toBe(true);
    });

    it("matches a loop with multiple iterations", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            < foo
            < foo
        `))).toBe(true);
    });

    it("fails if the loop body does not match", () => {
        const spec = build(loop(build(read(["foo"]))));
        expect(checkTranscript(spec, parseTranscript(`
            < bar
        `))).toBe(false);
    });

    it("fails when stopping in the middle of an iteration", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
        `))).toBe(false);
    });

    it("matches after a complete iteration", () => {
        const spec = build(loop(build(sequence(read(["foo"]), write(["bar"])))));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            > bar
        `))).toBe(true);
    });
});

describe("BorrowableSpec", () => {
    it("matches 0 iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(``))).toBe(true);
    });

    it("matches 1 iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
            < restore
        `))).toBe(true);
    });

    it("matches multiple iterations", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
            < restore
            < borrow
            > value
            < restore
        `))).toBe(true);
    });

    it("fails when stopping early in an iteration", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            > value
        `))).toBe(false);
    });

    it("fails with incorrect kind for a step", () => {
        expect(checkTranscript(BorrowableSpec, parseTranscript(`
            < borrow
            < value
            < restore
        `))).toBe(false);
    });
});

describe("checkTranscript with continuations", () => {
    it("matches concurrent specs with interleaved entries and continuation", () => {
        const spec = build(sequence(
            concurrent({
                left: build(read(["foo"])),
                right: build(write(["bar"]))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < left.foo
            > right.bar
            < next
        `))).toBe(true);
    });

    it("matches choice specs with continuation", () => {
        const spec = build(sequence(
            choice({
                ok: build(read(["data"])),
                err: build(read(["msg"]))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < data
            < next
        `))).toBe(true);
    });

    it("matches loop with continuation", () => {
        const spec = build(sequence(
            loop(build(read(["foo"]))),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            < next
        `))).toBe(true);
    });

    it("does not require key prefix for choice branches anymore", () => {
        const spec = build(sequence(
            choice({
                ok: build(sequence(read(["data1"]), read(["data2"])))
            }),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < data1
            < data2
            < next
        `))).toBe(true);
    });
});

describe("pairBorrowableCopyable", () => {
    const spec = build(pairBorrowableCopyable);

    it("matches zero iterations of all component loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > leftCmp.get
            < leftCmp.return
            > rightCmp.get
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("matches with active iterations and nested loops", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get

            > leftCmp.get
            < leftCmp.left.borrow
            > left.left.borrow
            < left.left.value
            > leftCmp.left.value
            < leftCmp.left.restore
            > left.left.restore

            < leftCmp.right.borrow
            > right.left.borrow
            > leftCmp.right.value
            < right.left.value
            < leftCmp.right.restore
            > right.left.restore

            < leftCmp.right.borrow
            > right.left.borrow
            > leftCmp.right.value
            < right.left.value
            < leftCmp.right.restore
            > right.left.restore
            < leftCmp.return

            > rightCmp.get
            < rightCmp.return
            > return
        `))).toBe(true);
    });

    it("fails if attempting to transition sub-component before starting comparator", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > leftCmp.left.borrow
        `))).toBe(false);
    });

    it("fails if loop iterations are incomplete", () => {
        expect(checkTranscript(spec, parseTranscript(`
            < get
            > left.left.borrow
            > leftCmp.get
        `))).toBe(false);
    });
});

describe("checkTranscript with complement", () => {
    it("reverses reads and writes", () => {
        const spec = build(complement(build(sequence(
            read(["foo"]),
            write(["bar"])
        ))));
        // read becomes write, write becomes read
        expect(checkTranscript(spec, parseTranscript(`
            > foo
            < bar
        `))).toBe(true);

        // does not match if directions are not reversed
        expect(checkTranscript(spec, parseTranscript(`
            < foo
            > bar
        `))).toBe(false);
    });

    it("works with nested loops and continuations", () => {
        const spec = build(sequence(
            complement(build(loop(build(sequence(
                read(["foo"]),
                write(["bar"])
            ))))),
            read(["next"])
        ));
        // loop body: read(foo) -> write(bar).
        // Under complement: write(foo) -> read(bar).
        expect(checkTranscript(spec, parseTranscript(`
            > foo
            < bar
            > foo
            < bar
            < next
        `))).toBe(true);
    });
});

describe("checkTranscript with prefix", () => {
    it("prefixes read and write channels", () => {
        const spec = build(prefix(["a", "b"], build(sequence(
            read(["c"]),
            write(["d"])
        ))));
        expect(checkTranscript(spec, parseTranscript(`
            < a.b.c
            > a.b.d
        `))).toBe(true);

        // fails if prefix is incorrect
        expect(checkTranscript(spec, parseTranscript(`
            < c
            > d
        `))).toBe(false);
    });

    it("works with nested prefixing", () => {
        const spec = build(prefix(["a"], build(prefix(["b"], build(read(["c"]))))));
        expect(checkTranscript(spec, parseTranscript(`
            < a.b.c
        `))).toBe(true);
    });

    it("works with loops and continuations", () => {
        const spec = build(sequence(
            prefix(["a"], build(loop(build(read(["b"]))))),
            read(["next"])
        ));
        expect(checkTranscript(spec, parseTranscript(`
            < a.b
            < a.b
            < next
        `))).toBe(true);
    });
});

describe("static validation (LL-1)", () => {
    it("throws error for ambiguous choice branches", () => {
        expect(() => {
            build(choice({
                branch1: build(read(["foo"])),
                branch2: build(read(["foo"]))
            }));
        }).toThrow(/Ambiguity detected in choice/);
    });

    it("throws error for ambiguous loop and continuation", () => {
        expect(() => {
            build(sequence(
                loop(build(read(["foo"]))),
                read(["foo"])
            ));
        }).toThrow(/Ambiguity detected in loop/);
    });

    it("allows non-overlapping choice branches", () => {
        expect(() => {
            build(choice({
                branch1: build(read(["foo"])),
                branch2: build(read(["bar"]))
            }));
        }).not.toThrow();
    });

    it("allows non-overlapping loop and continuation", () => {
        expect(() => {
            build(sequence(
                loop(build(read(["foo"]))),
                read(["bar"])
            ));
        }).not.toThrow();
    });
});

describe("isSubtype", () => {
    it("is reflexive (spec is subtype of itself)", () => {
        const spec = build(sequence(read(["foo"]), write(["bar"])));
        expect(isSubtype(spec, spec)).toBe(true);
        
        const loopSpec = BorrowableSpec;
        expect(isSubtype(loopSpec, loopSpec)).toBe(true);
    });

    it("supports contravariant inputs (reads)", () => {
        // A accepts more inputs than B. A is a subtype of B.
        const a = build(choice({
            ok: build(read(["data"])),
            err: build(read(["msg"]))
        }));
        const b = build(choice({
            ok: build(read(["data"]))
        }));
        expect(isSubtype(a, b)).toBe(true);
        expect(isSubtype(b, a)).toBe(false);
    });

    it("supports covariant outputs (writes)", () => {
        // A produces fewer outputs than B. A is a subtype of B.
        const a = build(choice({
            ok: build(write(["data"]))
        }));
        const b = build(choice({
            ok: build(write(["data"])),
            err: build(write(["msg"]))
        }));
        expect(isSubtype(a, b)).toBe(true);
        expect(isSubtype(b, a)).toBe(false);
    });

    it("respects completion constraints", () => {
        const a = build(read(["foo"]));
        const b = { kind: "done" } as MachineSpec;
        expect(isSubtype(a, b)).toBe(false);
        expect(isSubtype(b, a)).toBe(false);
        
        // done is a subtype of write(foo) because outputting nothing is a subset of outputting foo
        const c = build(write(["foo"]));
        expect(isSubtype(b, c)).toBe(true);
    });

    it("terminates and validates recursive specs (loops)", () => {
        const a = build(loop(build(read(["x"]))));
        const b = build(loop(build(read(["x"]))));
        expect(isSubtype(a, b)).toBe(true);
        
        const loopMore = build(loop(build(choice({
            x: build(read(["x"])),
            y: build(read(["y"]))
        }))));
        const loopLess = build(loop(build(read(["x"]))));
        expect(isSubtype(loopMore, loopLess)).toBe(true);
        expect(isSubtype(loopLess, loopMore)).toBe(false);
    });

    it("verifies sequential borrowable uses can subtype a single concurrent borrowable", () => {
        // A single sequential worker that performs two borrows inline,
        // separated by an intermediate action.
        const subtype = build(sequence(
            read(["main", "request"]),
            write(["val1", "borrow"]),
            read(["val1", "value"]),
            write(["main", "partial response"]),  // NOTE: we're very sensitive to the placement of this.
            write(["val2", "borrow"]),
            read(["val2", "value"]),
            write(["val2", "restore"]),
            write(["val1", "restore"]),
            write(["main", "response"]),
        ));
        
        // A version of subtype with all the "borrowable" stuff factored out.
        const factoredSubtype = build(sequence(
            read(["request"]),
            write(["partial response"]),
            write(["response"]),
        ));
        
        const supertype = build(concurrent({
            main: factoredSubtype,
            val1: build(complement(BorrowableSpec)),
            val2: build(complement(BorrowableSpec)),
        }));
        
        expect(isSubtype(subtype, supertype)).toBe(true);
    });

    it("verifies sequential borrowable uses can subtype a single concurrent borrowable in a loop", () => {
        // A single sequential worker that performs two borrows inline,
        // separated by an intermediate action.
        const subtype = build(loop(build(sequence(
            read(["main", "request"]),
            write(["val1", "borrow"]),
            read(["val1", "value"]),
            write(["main", "partial response"]),  // NOTE: we're very sensitive to the placement of this.
            write(["val2", "borrow"]),
            read(["val2", "value"]),
            write(["val2", "restore"]),
            write(["val1", "restore"]),
            write(["main", "response"]),
        ))));
        
        // A version of subtype with all the "borrowable" stuff factored out.
        const factoredSubtype = build(loop(build(sequence(
            read(["request"]),
            write(["partial response"]),
            write(["response"]),
        ))));
        
        const supertype = build(concurrent({
            main: factoredSubtype,
            val1: build(complement(BorrowableSpec)),
            val2: build(complement(BorrowableSpec)),
        }));
        
        expect(isSubtype(subtype, supertype)).toBe(true);
    });
});

describe("parseTranscript", () => {
    it("parses read and write lines with period separators", () => {
        const text = `
            < foo.bar
            > baz.qux.quux
        `;
        expect(parseTranscript(text)).toEqual([
            { kind: "read", channel: ["foo", "bar"] },
            { kind: "write", channel: ["baz", "qux", "quux"] },
        ]);
    });

    it("handles trailing and leading whitespaces properly", () => {
        const text = "  <   a . b   \n  >  c  ";
        expect(parseTranscript(text)).toEqual([
            { kind: "read", channel: ["a", "b"] },
            { kind: "write", channel: ["c"] },
        ]);
    });

    it("ignores empty lines", () => {
        expect(parseTranscript("   \n\n  \n")).toEqual([]);
    });

    it("throws on invalid action prefix", () => {
        expect(() => parseTranscript("foo.bar")).toThrow();
        expect(() => parseTranscript("? foo.bar")).toThrow();
    });

    it("throws on missing channel name", () => {
        expect(() => parseTranscript("<")).toThrow();
        expect(() => parseTranscript(">   ")).toThrow();
    });

    it("throws on empty channel segments", () => {
        expect(() => parseTranscript("< foo..bar")).toThrow();
        expect(() => parseTranscript("< .")).toThrow();
    });
});