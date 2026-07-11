import {
    MachineSpec2,
    read,
    write,
    sequence,
    choice,
    star,
    concurrent,
    complement,
    rename,
    prefix,
    indexed,
    trace,
    isCompleted,
    transition,
    getPossibleTransitions,
    checkTranscript,
    parseTranscript,
    serializeSpec,
    compile,
    serializeCompiledSpec,
    isSubtype
} from "./spec2";

describe("MachineSpec2 constructors & serialization", () => {
    it("creates read and write specs", () => {
        expect(read(["a"])).toEqual({ kind: "read", channel: ["a"] });
        expect(write(["b"])).toEqual({ kind: "write", channel: ["b"] });
    });

    it("creates simplified variadic sequence", () => {
        expect(sequence()).toEqual({ kind: "sequence", specs: [] });
        expect(sequence(read(["a"]))).toEqual({ kind: "read", channel: ["a"] });
        expect(sequence(read(["a"]), write(["b"]))).toEqual({
            kind: "sequence",
            specs: [
                { kind: "read", channel: ["a"] },
                { kind: "write", channel: ["b"] }
            ]
        });
        // empty sequence elements are automatically flattened/simplified
        expect(sequence(read(["a"]), sequence(), write(["b"]))).toEqual({
            kind: "sequence",
            specs: [
                { kind: "read", channel: ["a"] },
                { kind: "write", channel: ["b"] }
            ]
        });
    });

    it("creates simplified variadic choice", () => {
        expect(choice(read(["a"]))).toEqual({ kind: "read", channel: ["a"] });
        expect(choice(read(["a"]), write(["b"]))).toEqual({
            kind: "choice",
            choices: [
                { kind: "read", channel: ["a"] },
                { kind: "write", channel: ["b"] }
            ]
        });
        // nested choice elements are automatically flattened
        expect(choice(read(["a"]), choice(write(["b"]), read(["c"])))).toEqual({
            kind: "choice",
            choices: [
                { kind: "read", channel: ["a"] },
                { kind: "write", channel: ["b"] },
                { kind: "read", channel: ["c"] }
            ]
        });
    });

    it("creates concurrent specs", () => {
        expect(concurrent({
            left: read(["foo"]),
            right: write(["bar"])
        })).toEqual({
            kind: "concurrent",
            machines: {
                left: { kind: "read", channel: ["foo"] },
                right: { kind: "write", channel: ["bar"] }
            }
        });
    });

    it("creates complement and rename specs", () => {
        expect(complement(read(["foo"]))).toEqual({
            kind: "complement",
            inner: { kind: "read", channel: ["foo"] }
        });
        // double complement is simplified away
        expect(complement(complement(read(["foo"])))).toEqual({
            kind: "read",
            channel: ["foo"]
        });

        expect(rename([ [["a"], ["b"]] ], read(["a"]))).toEqual({
            kind: "rename",
            mapping: [ [["a"], ["b"]] ],
            inner: { kind: "read", channel: ["a"] }
        });
        // empty mapping rename is simplified away
        expect(rename([], read(["a"]))).toEqual({
            kind: "read",
            channel: ["a"]
        });
    });

    it("creates prefix specs", () => {
        expect(prefix(["main"], read(["foo"]))).toEqual({
            kind: "prefix",
            prefix: ["main"],
            inner: { kind: "read", channel: ["foo"] }
        });
        // empty prefix is simplified away
        expect(prefix([], read(["foo"]))).toEqual({
            kind: "read",
            channel: ["foo"]
        });
        // nested prefixes are flattened
        expect(prefix(["a"], prefix(["b"], read(["foo"])))).toEqual({
            kind: "prefix",
            prefix: ["a", "b"],
            inner: { kind: "read", channel: ["foo"] }
        });
    });

    it("creates indexed and trace specs", () => {
        expect(indexed(read(["foo"]))).toEqual({
            kind: "indexed",
            inner: { kind: "read", channel: ["foo"] },
            active: []
        });

        expect(trace(["left"], ["right"], read(["foo"]))).toEqual({
            kind: "trace",
            inner: { kind: "read", channel: ["foo"] },
            pathA: ["left"],
            pathB: ["right"]
        });
    });

    it("serializes specs properly", () => {
        const spec = sequence(read(["a"]), choice(write(["b"]), star(read(["c"]))));
        expect(serializeSpec(spec)).toBe("seq(read(a),choice(write(b),star(read(c))))");

        const spec2 = concurrent({ left: read(["foo"]), right: write(["bar"]) });
        expect(serializeSpec(spec2)).toBe("concurrent({left:read(foo),right:write(bar)})");

        const spec3 = rename([ [["c"], ["in"]], [["d"], ["out"]] ], sequence(read(["c"]), write(["d"])));
        expect(serializeSpec(spec3)).toBe("rename({c:in,d:out},seq(read(c),write(d)))");

        const spec4 = prefix(["main"], read(["foo"]));
        expect(serializeSpec(spec4)).toBe("prefix(main,read(foo))");

        const spec5 = indexed(read(["foo"]));
        expect(serializeSpec(spec5)).toBe("indexed(read(foo))");

        const spec6 = trace(["left"], ["right"], read(["foo"]));
        expect(serializeSpec(spec6)).toBe("trace(read(foo),left,right)");
    });
});

describe("isCompleted", () => {
    it("identifies nullable specs", () => {
        expect(isCompleted(sequence())).toBe(true);
        expect(isCompleted(read(["a"]))).toBe(false);
        expect(isCompleted(star(read(["a"])))).toBe(true);
        expect(isCompleted(sequence(sequence(), star(read(["a"]))))).toBe(true);
        expect(isCompleted(sequence(read(["a"]), star(read(["b"]))))).toBe(false);
        expect(isCompleted(choice(read(["a"]), sequence()))).toBe(true);
        // empty choice should never be completed
        expect(isCompleted(choice())).toBe(false);
        // concurrent completed if all components are completed
        expect(isCompleted(concurrent({ left: star(read(["a"])), right: sequence() }))).toBe(true);
        expect(isCompleted(concurrent({ left: read(["a"]), right: sequence() }))).toBe(false);
        // complement, rename, prefix, indexed pass through completion status
        expect(isCompleted(complement(read(["a"])))).toBe(false);
        expect(isCompleted(complement(star(read(["a"]))))).toBe(true);
        expect(isCompleted(prefix(["main"], read(["a"])))).toBe(false);
        expect(isCompleted(prefix(["main"], star(read(["a"]))))).toBe(true);
        expect(isCompleted(indexed(read(["a"])))).toBe(true);
    });
});

describe("getPossibleTransitions", () => {
    it("gets first events", () => {
        const spec = choice(
            sequence(read(["a"]), write(["b"])),
            sequence(write(["c"]), read(["d"]))
        );
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["a"] },
            { kind: "write", channel: ["c"] }
        ]);
    });

    it("includes transitions after nullable sequence left", () => {
        const spec = sequence(star(read(["a"])), write(["b"]));
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["a"] },
            { kind: "write", channel: ["b"] }
        ]);
    });

    it("prefixes transitions for concurrent specs", () => {
        const spec = concurrent({
            left: read(["foo"]),
            right: write(["bar"])
        });
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["left", "foo"] },
            { kind: "write", channel: ["right", "bar"] }
        ]);
    });

    it("reverses kinds for complement transitions", () => {
        const spec = complement(choice(read(["foo"]), write(["bar"])));
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "write", channel: ["foo"] },
            { kind: "read", channel: ["bar"] }
        ]);
    });

    it("maps channels for rename transitions", () => {
        const spec = rename([ [["c"], ["in"]], [["d"], ["out"]] ], choice(read(["c"]), write(["d"])));
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["in"] },
            { kind: "write", channel: ["out"] }
        ]);
    });

    it("prefixes channels for prefix transitions", () => {
        const spec = prefix(["main"], choice(read(["foo"]), write(["bar"])));
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["main", "foo"] },
            { kind: "write", channel: ["main", "bar"] }
        ]);
    });

    it("gets transitions for indexed specs with wildcard", () => {
        const spec = indexed(read(["foo"]));
        expect(getPossibleTransitions(spec)).toEqual([
            { kind: "read", channel: ["*", "foo"] }
        ]);
    });
});

describe("checkTranscript on CompiledSpec", () => {
    it("matches basic sequence", () => {
        const spec = sequence(read(["a"]), write(["b"]));
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            > b
        `))).toBe(true);

        expect(checkTranscript(compiled, parseTranscript(`
            < a
        `))).toBe(false);
    });

    it("matches star loops", () => {
        const spec = star(sequence(read(["a"]), write(["b"])));
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(``))).toBe(true);
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            > b
        `))).toBe(true);
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            > b
            < a
            > b
        `))).toBe(true);
    });

    it("handles non-deterministic choice", () => {
        const spec = choice(
            sequence(read(["a"]), read(["b"])),
            sequence(read(["a"]), read(["c"]))
        );
        const compiled = compile(spec);

        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < b
        `))).toBe(true);

        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < c
        `))).toBe(true);

        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < d
        `))).toBe(false);
    });

    it("handles non-deterministic loops", () => {
        const spec = sequence(
            star(read(["a"])),
            read(["a"])
        );
        const compiled = compile(spec);

        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < a
            < a
        `))).toBe(true);
    });

    it("matches concurrent specs with interleaved entries", () => {
        const spec = concurrent({
            left: read(["foo"]),
            right: write(["bar"])
        });
        const compiled = compile(spec);

        // interleaved 1
        expect(checkTranscript(compiled, parseTranscript(`
            < left.foo
            > right.bar
        `))).toBe(true);

        // interleaved 2
        expect(checkTranscript(compiled, parseTranscript(`
            > right.bar
            < left.foo
        `))).toBe(true);
    });

    it("matches complement spec transitions", () => {
        const spec = complement(sequence(read(["a"]), write(["b"])));
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(`
            > a
            < b
        `))).toBe(true);
    });

    it("matches rename spec transitions", () => {
        const spec = rename([ [["c"], ["in"]], [["d"], ["out"]] ], sequence(read(["c"]), write(["d"])));
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(`
            < in
            > out
        `))).toBe(true);
    });

    it("matches prefix spec transitions", () => {
        const spec = prefix(["main"], sequence(read(["foo"]), write(["bar"])));
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(`
            < main.foo
            > main.bar
        `))).toBe(true);
    });

    it("matches indexed spec transitions dynamically", () => {
        const spec = indexed(sequence(read(["foo"]), write(["bar"])));
        const compiled = compile(spec);
        // Can launch instance 1 and instance 2 concurrently and interleave them
        expect(checkTranscript(compiled, parseTranscript(`
            < conn1.foo
            < conn2.foo
            > conn2.bar
            > conn1.bar
        `))).toBe(true);
    });

    it("matches trace spec transitions and hides internal ones", () => {
        const inner = concurrent({
            prod: write(["mid"]),
            cons: sequence(read(["mid"]), write(["out"]))
        });
        const spec = trace(["prod", "mid"], ["cons", "mid"], inner);
        const compiled = compile(spec);
        expect(checkTranscript(compiled, parseTranscript(`
            > cons.out
        `))).toBe(true);
    });
});

describe("compile to DFA (CompiledSpec)", () => {
    it("compiles a simple sequence", () => {
        const spec = sequence(read(["a"]), write(["b"]));
        const compiled = compile(spec);
        expect(serializeCompiledSpec(compiled)).toBe(
            "0: [read(a)->1]\n" +
            "1: [write(b)->2]\n" +
            "2*: []"
        );
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            > b
        `))).toBe(true);
    });

    it("compiles ambiguous choices into a DFA", () => {
        const spec = choice(
            sequence(read(["a"]), read(["b"])),
            sequence(read(["a"]), read(["c"]))
        );
        const compiled = compile(spec);
        expect(serializeCompiledSpec(compiled)).toBe(
            "0: [read(a)->1]\n" +
            "1: [read(b)->2, read(c)->2]\n" +
            "2*: []"
        );
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < b
        `))).toBe(true);
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            < c
        `))).toBe(true);
    });

    it("compiles star loops into a DFA", () => {
        const spec = star(sequence(read(["a"]), write(["b"])));
        const compiled = compile(spec);
        expect(serializeCompiledSpec(compiled)).toBe(
            "0*: [read(a)->1]\n" +
            "1: [write(b)->0]"
        );
        expect(checkTranscript(compiled, parseTranscript(`
            < a
            > b
            < a
            > b
        `))).toBe(true);
    });
});

describe("isSubtype for CompiledSpec", () => {
    it("is reflexive (spec is subtype of itself)", () => {
        const spec = sequence(read(["foo"]), write(["bar"]));
        expect(isSubtype(compile(spec), compile(spec)).isSubtype).toBe(true);

        const loopSpec = star(sequence(read(["borrow"]), write(["value"]), read(["restore"])));
        expect(isSubtype(compile(loopSpec), compile(loopSpec)).isSubtype).toBe(true);
    });

    it("renamed spec is equivalent to direct outer-name representation", () => {
        const renamed = rename([ [["c"], ["in0"]], [["d"], ["out0"]] ], sequence(
            read(["c"]),
            write(["d"])
        ));
        const direct = sequence(
            read(["in0"]),
            write(["out0"])
        );
        expect(isSubtype(compile(renamed), compile(direct)).isSubtype).toBe(true);
        expect(isSubtype(compile(direct), compile(renamed)).isSubtype).toBe(true);
    });

    it("supports contravariant inputs (reads)", () => {
        // A accepts more inputs than B. A is a subtype of B.
        const a = choice(
            read(["data"]),
            read(["msg"])
        );
        const b = choice(
            read(["data"])
        );
        expect(isSubtype(compile(a), compile(b)).isSubtype).toBe(true);

        const res = isSubtype(compile(b), compile(a));
        expect(res.isSubtype).toBe(false);
        if (res.isSubtype === false) {
            expect(res.reason).toBe("read");
            expect(res.transcript).toEqual(parseTranscript("< msg"));
        }
    });

    it("supports covariant outputs (writes)", () => {
        // A produces fewer outputs than B. A is a subtype of B.
        const a = choice(
            write(["data"])
        );
        const b = choice(
            write(["data"]),
            write(["msg"])
        );
        expect(isSubtype(compile(a), compile(b)).isSubtype).toBe(true);

        const res = isSubtype(compile(b), compile(a));
        expect(res.isSubtype).toBe(false);
        if (res.isSubtype === false) {
            expect(res.reason).toBe("write");
            expect(res.transcript).toEqual(parseTranscript("> msg"));
        }
    });

    it("respects completion constraints", () => {
        const a = read(["foo"]);
        const b = sequence(); // empty sequence

        const resAtoB = isSubtype(compile(a), compile(b));
        expect(resAtoB.isSubtype).toBe(false);
        if (resAtoB.isSubtype === false) {
            expect(resAtoB.reason).toBe("completion");
            expect(resAtoB.transcript).toEqual(parseTranscript(""));
        }

        const resBtoA = isSubtype(compile(b), compile(a));
        expect(resBtoA.isSubtype).toBe(false);
        if (resBtoA.isSubtype === false) {
            expect(resBtoA.reason).toBe("read");
            expect(resBtoA.transcript).toEqual(parseTranscript("< foo"));
        }

        // done is a subtype of write(foo) because outputting nothing is a subset of outputting foo
        const c = write(["foo"]);
        expect(isSubtype(compile(b), compile(c)).isSubtype).toBe(true);
    });

    it("terminates and validates recursive specs (loops)", () => {
        const a = star(read(["x"]));
        const b = star(read(["x"]));
        expect(isSubtype(compile(a), compile(b)).isSubtype).toBe(true);

        const loopMore = star(choice(
            read(["x"]),
            read(["y"])
        ));
        const loopLess = star(read(["x"]));
        expect(isSubtype(compile(loopMore), compile(loopLess)).isSubtype).toBe(true);

        const res = isSubtype(compile(loopLess), compile(loopMore));
        expect(res.isSubtype).toBe(false);
        if (res.isSubtype === false) {
            expect(res.reason).toBe("read");
            expect(res.transcript).toEqual(parseTranscript("< y"));
        }
    });

    it("returns correct nested path in a nested read mismatch", () => {
        const subtype = sequence(
            read(["step1"]),
            write(["step2"]),
            read(["step3"])
        );
        const supertype = sequence(
            read(["step1"]),
            write(["step2"]),
            read(["step4"])
        );
        const res = isSubtype(compile(subtype), compile(supertype));
        expect(res.isSubtype).toBe(false);
        if (res.isSubtype === false) {
            expect(res.reason).toBe("read");
            expect(res.transcript).toEqual(parseTranscript(`
                < step1
                > step2
                < step4
            `));
        }
    });

    it("returns correct nested path in a nested write mismatch", () => {
        const subtype = sequence(
            read(["step1"]),
            write(["step2"]),
            write(["step3"])
        );
        const supertype = sequence(
            read(["step1"]),
            write(["step2"]),
            write(["step4"])
        );
        const res = isSubtype(compile(subtype), compile(supertype));
        expect(res.isSubtype).toBe(false);
        if (res.isSubtype === false) {
            expect(res.reason).toBe("write");
            expect(res.transcript).toEqual(parseTranscript(`
                < step1
                > step2
                > step3
            `));
        }
    });
});
