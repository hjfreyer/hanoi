import { build, sequence, read, write, concurrent, choice, loop, complement } from "./spec";
import { Runtime, Machine } from "./impl";

describe("impl runtime and concrete computations", () => {
    it("runs a simple sequence of read and write and terminates", async () => {
        const spec = build(sequence(
            read(["a"]),
            write(["b"])
        ));

        const machine: Machine = async (ctx) => {
            const val = await ctx.read(["a"]);
            await ctx.write(["b"], val * 2);
        };

        const runtime = new Runtime(spec, machine);
        const runPromise = runtime.run();

        await runtime.externalWrite(["a"], 10);
        const result = await runtime.externalRead(["b"]);

        expect(result).toBe(20);
        await runPromise; // should resolve successfully
    });

    it("throws a spec violation error if machine does an unexpected write", async () => {
        const spec = build(sequence(
            read(["a"])
        ));

        const machine: Machine = async (ctx) => {
            await ctx.write(["invalid"], 42);
        };

        const runtime = new Runtime(spec, machine);
        const runPromise = runtime.run();

        await expect(runPromise).rejects.toThrow(/Spec violation/);
    });

    it("handles choices using select", async () => {
        const spec = build(sequence(
            choice({
                ok: build(read(["data"])),
                err: build(read(["error"]))
            }),
            write(["done"])
        ));

        const machine: Machine = async (ctx) => {
            const selected = await ctx.select([
                {
                    kind: "read",
                    channel: ["data"],
                    callback: (val) => ({ status: "ok", value: val })
                },
                {
                    kind: "read",
                    channel: ["error"],
                    callback: (err) => ({ status: "err", value: err })
                }
            ]);

            await ctx.write(["done"], selected);
        };

        // Test ok branch
        {
            const runtime = new Runtime(spec, machine);
            const runPromise = runtime.run();
            await runtime.externalWrite(["data"], "hello");
            const result = await runtime.externalRead(["done"]);
            expect(result).toEqual({ status: "ok", value: "hello" });
            await runPromise;
        }

        // Test err branch
        {
            const runtime = new Runtime(spec, machine);
            const runPromise = runtime.run();
            await runtime.externalWrite(["error"], "oops");
            const result = await runtime.externalRead(["done"]);
            expect(result).toEqual({ status: "err", value: "oops" });
            await runPromise;
        }
    });

    it("handles loops with termination", async () => {
        const spec = build(sequence(
            loop(build(read(["step"]))),
            write(["finished"])
        ));

        const machine: Machine = async (ctx) => {
            // Read "step" up to 3 times, then stop
            for (let i = 0; i < 3; i++) {
                await ctx.read(["step"]);
            }
            await ctx.write(["finished"], "yes");
        };

        const runtime = new Runtime(spec, machine);
        const runPromise = runtime.run();

        await runtime.externalWrite(["step"], 1);
        await runtime.externalWrite(["step"], 2);
        await runtime.externalWrite(["step"], 3);
        const res = await runtime.externalRead(["finished"]);
        expect(res).toBe("yes");
        await runPromise;
    });

    it("supports concurrent sub-machines and wiring duals", async () => {
        // Spec has concurrent left (client) and right (provider)
        // client: complement(BorrowSpec) -> write(borrow), read(value), write(restore)
        // provider: BorrowSpec -> read(borrow), write(value), read(restore)
        const BorrowSpec = build(sequence(
            read(["borrow"]),
            write(["value"]),
            read(["restore"])
        ));

        const spec = build(concurrent({
            client: build(complement(BorrowSpec)),
            provider: BorrowSpec
        }));

        const clientMachine: Machine = async (ctx) => {
            await ctx.write(["borrow"], "please");
            const val = await ctx.read(["value"]);
            expect(val).toBe("borrowed-token");
            await ctx.write(["restore"], "thanks");
        };

        const providerMachine: Machine = async (ctx) => {
            const req = await ctx.read(["borrow"]);
            expect(req).toBe("please");
            await ctx.write(["value"], "borrowed-token");
            const res = await ctx.read(["restore"]);
            expect(res).toBe("thanks");
        };

        const mainMachine: Machine = async (ctx) => {
            ctx.spawn("client", clientMachine);
            ctx.spawn("provider", providerMachine);
        };

        const runtime = new Runtime(spec, mainMachine);
        // Wire the client channels to provider channels
        runtime.wire(["client", "borrow"], ["provider", "borrow"]);
        runtime.wire(["client", "value"], ["provider", "value"]);
        runtime.wire(["client", "restore"], ["provider", "restore"]);

        await runtime.run(); // Should complete successfully because all channels wired and duals match
    });
});
