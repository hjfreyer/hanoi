import { Value, ValueSet } from "./value"

export type MachineSpec =
  | { kind: "done" }
  | { kind: "read"; channel: ValueSet; next: string}
  | { kind: "write"; channel: ValueSet; next: string }
  | { kind: "externalChoice"; choices: MachineSpec[] }
  | { kind: "internalChoice"; choices: MachineSpec[] }
  | { kind: "concurrent"; machines: MachineSpec[] };


