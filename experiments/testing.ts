import { MachineInstance, StepResult, RenameMachine } from "./impl";
import { MachineSpec } from "./spec";
import { ValueCellMachine } from "./primitives";

export class Runner {
  private state: any;
  constructor(private machine: MachineInstance) {
    this.state = machine.createState();
  }
  isCompleted(): boolean {
    return this.machine.isCompleted(this.state);
  }
  getSpec(): MachineSpec {
    return this.machine.getSpec();
  }
  step(action?: { channel: string[]; value?: any }): StepResult {
    const { result, state } = this.machine.step(this.state, action);
    this.state = state;
    return result;
  }
  run(action?: { channel: string[]; value?: any }): StepResult[] {
    const results: StepResult[] = [];
    let res = this.step(action);
    if (res.kind === "waiting") {
      return results;
    }
    results.push(res);
    while (res.kind !== "waiting" && res.kind !== "done") {
      res = this.step();
      if (res.kind !== "waiting") {
        results.push(res);
      }
    }
    return results;
  }
  getState(): any {
    return this.state;
  }
  getValue(): any {
    if ("getValue" in this.machine) {
      return (this.machine as any).getValue(this.state);
    }
    throw new Error("getValue not supported on this machine");
  }
}

export function makeUnindexedCell(cell: ValueCellMachine): RenameMachine {
  return new RenameMachine(cell, [
    [["p0", "copy"], ["copy"]],
    [["p0", "value"], ["value"]],
    [["p0", "set"], ["set"]],
  ]);
}
