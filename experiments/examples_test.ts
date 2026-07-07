import { build, sequence, read, write, choice, loop, parseTranscript, checkTranscript } from "./spec";
import { Runtime, Machine } from "./impl";

// 1. Define the ValueCell spec
export const ValueCellSpec = build(loop(build(choice({
    set: build(read(["set"])),
    copy: build(sequence(
        read(["copy"]),
        write(["value"])
    ))
}))));

// 2. Implement the ValueCell machine
export const valueCellMachine = (initialValue: any): Machine => {
    return async (ctx) => {
        let value = initialValue;
        while (true) {
            type Action = 
                | { type: "set"; value: any }
                | { type: "copy" };

            const action = await ctx.select<Action>([
                {
                    kind: "read",
                    channel: ["set"],
                    callback: (val) => ({ type: "set" as const, value: val })
                },
                {
                    kind: "read",
                    channel: ["copy"],
                    callback: () => ({ type: "copy" as const })
                }
            ]);

            if (action.type === "set") {
                value = action.value;
            } else if (action.type === "copy") {
                await ctx.write(["value"], value);
            }
        }
    };
};

describe("ValueCell example", () => {
    it("can set and copy values", async () => {
        const runtime = new Runtime(ValueCellSpec, valueCellMachine(42));
        const runPromise = runtime.run();

        // Initially copy should return 42
        await runtime.externalWrite(["copy"], null);
        const val1 = await runtime.externalRead(["value"]);
        expect(val1).toBe(42);

        // Set value to 100 directly on the ["set"] channel
        await runtime.externalWrite(["set"], 100);

        // Copy should now return 100
        await runtime.externalWrite(["copy"], null);
        const val2 = await runtime.externalRead(["value"]);
        expect(val2).toBe(100);
    });

    it("verifies a valid execution transcript against ValueCellSpec", () => {
        const transcript = parseTranscript(`
            < copy
            > value
            < set
            < copy
            > value
        `);
        expect(checkTranscript(ValueCellSpec, transcript)).toBe(true);
    });
});

// 3. Define the UninitValueCell spec
export const UninitValueCellSpec = build(sequence(
    read(["set"]),
    loop(build(choice({
        set: build(read(["set"])),
        copy: build(sequence(
            read(["copy"]),
            write(["value"])
        ))
    })))
));

// 4. Implement the UninitValueCell machine
export const uninitValueCellMachine: Machine = async (ctx) => {
    // Force set before first copy
    const initialVal = await ctx.read(["set"]);
    // Delegate to the normal valueCellMachine behavior
    await valueCellMachine(initialVal)(ctx);
};

describe("UninitValueCell example", () => {
    it("fails if machine tries to copy before set", async () => {
        const badMachine: Machine = async (ctx) => {
            await ctx.read(["copy"]);
        };
        const runtime = new Runtime(UninitValueCellSpec, badMachine);
        // The machine's unexpected read on ["copy"] should violate the spec immediately
        await expect(runtime.run()).rejects.toThrow(/Spec violation/);
    });

    it("can set first and then copy", async () => {
        const runtime = new Runtime(UninitValueCellSpec, uninitValueCellMachine);
        const runPromise = runtime.run();

        // Set value to 25
        await runtime.externalWrite(["set"], 25);

        // Now copy should succeed and return 25
        await runtime.externalWrite(["copy"], null);
        const val = await runtime.externalRead(["value"]);
        expect(val).toBe(25);
    });

    it("verifies transcripts against UninitValueCellSpec", () => {
        const valid = parseTranscript(`
            < set
            < copy
            > value
        `);
        expect(checkTranscript(UninitValueCellSpec, valid)).toBe(true);

        const invalid = parseTranscript(`
            < copy
            > value
            < set
        `);
        expect(checkTranscript(UninitValueCellSpec, invalid)).toBe(false);
    });
});
