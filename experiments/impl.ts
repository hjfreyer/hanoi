import {
  MachineSpec,
  transition,
  isCompleted,
  read,
  write,
  loop,
  concurrent,
  sequence,
  getPossibleTransitions,
} from "./spec";

export type StepResult =
  | { kind: "write"; channel: string[]; value: any }
  | { kind: "read"; channel: string[]; value: any }
  | { kind: "waiting" }
  | { kind: "done" };

export interface MachineInstance {
  createState(): any;
  getSpec(): MachineSpec;
  isCompleted(state: any): boolean;
  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any };
}

export function concatSpecs(a: MachineSpec, b: MachineSpec): MachineSpec {
  return sequence(a, b);
}

export class SequenceMachine implements MachineInstance {
  private machines: MachineInstance[];

  constructor(machines: MachineInstance[]) {
    this.machines = machines;
  }

  createState(): any {
    return {
      currentIndex: 0,
      states: this.machines.map((m) => m.createState()),
    };
  }

  getSpec(): MachineSpec {
    return sequence(...this.machines.map((m) => m.getSpec()));
  }

  isCompleted(state: any): boolean {
    return (
      state.currentIndex >= this.machines.length ||
      this.machines
        .slice(state.currentIndex)
        .every((m, idx) =>
          m.isCompleted(state.states[state.currentIndex + idx]),
        )
    );
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.currentIndex >= this.machines.length) {
      return { result: { kind: "done" }, state };
    }

    const active = this.machines[state.currentIndex];
    const activeState = state.states[state.currentIndex];
    const { result, state: nextActiveState } = active.step(activeState, action);

    const nextStates = [...state.states];
    nextStates[state.currentIndex] = nextActiveState;
    const nextState = {
      ...state,
      states: nextStates,
    };

    if (result.kind === "done") {
      const nextSeqState = {
        ...nextState,
        currentIndex: state.currentIndex + 1,
      };
      return this.step(nextSeqState, action);
    }
    return { result, state: nextState };
  }
}

export class ConcurrentMachine implements MachineInstance {
  private machines: Record<string, MachineInstance>;

  constructor(machines: Record<string, MachineInstance>) {
    this.machines = machines;
  }

  createState(): any {
    const states: Record<string, any> = {};
    for (const [key, sub] of Object.entries(this.machines)) {
      states[key] = sub.createState();
    }
    return { states };
  }

  getSpec(): MachineSpec {
    const subSpecs: Record<string, MachineSpec> = {};
    for (const [key, sub] of Object.entries(this.machines)) {
      subSpecs[key] = sub.getSpec();
    }
    return {
      kind: "concurrent",
      machines: subSpecs,
    };
  }

  isCompleted(state: any): boolean {
    return Object.entries(this.machines).every(([key, sub]) =>
      sub.isCompleted(state.states[key]),
    );
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action && action.channel.length > 0) {
      const key = action.channel[0];
      const sub = this.machines[key];
      if (!sub) {
        return { result: { kind: "waiting" }, state };
      }
      const activeState = state.states[key];
      const { result, state: nextActiveState } = sub.step(activeState, {
        channel: action.channel.slice(1),
        value: action.value,
      });

      const nextStates = {
        ...state.states,
        [key]: nextActiveState,
      };
      const nextState = { ...state, states: nextStates };

      if (result.kind === "read" || result.kind === "write") {
        return {
          result: {
            ...result,
            channel: [key, ...result.channel],
          },
          state: nextState,
        };
      }
      return { result, state: nextState };
    }

    // Try to let sub-machines perform writes
    let currentStates = { ...state.states };
    for (const [key, sub] of Object.entries(this.machines)) {
      const activeState = currentStates[key];
      if (sub.isCompleted(activeState)) continue;
      const { result, state: nextActiveState } = sub.step(activeState);
      currentStates[key] = nextActiveState;
      if (result.kind === "write") {
        return {
          result: {
            kind: "write",
            channel: [key, ...result.channel],
            value: result.value,
          },
          state: { ...state, states: currentStates },
        };
      }
    }

    if (this.isCompleted({ ...state, states: currentStates })) {
      return {
        result: { kind: "done" },
        state: { ...state, states: currentStates },
      };
    }

    return {
      result: { kind: "waiting" },
      state: { ...state, states: currentStates },
    };
  }
}

export function channelsEqual(a: string[], b: string[]): boolean {
  if (a.length !== b.length) return false;
  return a.every((val, index) => val === b[index]);
}

function getSuffix(channel: string[], prefix: string[]): string[] | null {
  if (channel.length < prefix.length) return null;
  for (let i = 0; i < prefix.length; i++) {
    if (channel[i] !== prefix[i]) return null;
  }
  return channel.slice(prefix.length);
}

export class TraceMachine implements MachineInstance {
  private inner: MachineInstance;
  private pathA: string[];
  private pathB: string[];

  constructor(inner: MachineInstance, pathA: string[], pathB: string[]) {
    this.inner = inner;
    this.pathA = pathA;
    this.pathB = pathB;
  }

  createState(): any {
    return {
      innerState: this.inner.createState(),
    };
  }

  getSpec(): MachineSpec {
    return {
      kind: "trace",
      inner: this.inner.getSpec(),
      pathA: this.pathA,
      pathB: this.pathB,
    };
  }

  isCompleted(state: any): boolean {
    return this.inner.isCompleted(state.innerState);
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    let innerState = state.innerState;
    let res: StepResult;

    if (action) {
      const stepRes = this.inner.step(innerState, action);
      res = stepRes.result;
      innerState = stepRes.state;
    } else {
      const stepRes = this.inner.step(innerState);
      res = stepRes.result;
      innerState = stepRes.state;
    }

    const processed = this.processInternal(innerState, res);
    return {
      result: processed.result,
      state: { ...state, innerState: processed.innerState },
    };
  }

  private processInternal(
    innerState: any,
    res: StepResult,
  ): { result: StepResult; innerState: any } {
    let current = res;
    let currentInnerState = innerState;
    while (true) {
      if (current.kind === "write") {
        const suffixA = getSuffix(current.channel, this.pathA);
        if (suffixA !== null) {
          const stepRes1 = this.inner.step(currentInnerState, {
            channel: [...this.pathB, ...suffixA],
            value: current.value,
          });
          const stepRes2 = this.inner.step(stepRes1.state);
          current = stepRes2.result;
          currentInnerState = stepRes2.state;
          continue;
        }
        const suffixB = getSuffix(current.channel, this.pathB);
        if (suffixB !== null) {
          const stepRes1 = this.inner.step(currentInnerState, {
            channel: [...this.pathA, ...suffixB],
            value: current.value,
          });
          const stepRes2 = this.inner.step(stepRes1.state);
          current = stepRes2.result;
          currentInnerState = stepRes2.state;
          continue;
        }
      }
      if (current.kind === "read") {
        if (
          getSuffix(current.channel, this.pathA) !== null ||
          getSuffix(current.channel, this.pathB) !== null
        ) {
          const stepRes = this.inner.step(currentInnerState);
          current = stepRes.result;
          currentInnerState = stepRes.state;
          continue;
        }
      }
      break;
    }
    return { result: current, innerState: currentInnerState };
  }
}

export class WriteConstantMachine implements MachineInstance {
  constructor(
    private channel: string[],
    private value: any,
  ) {}

  createState(): any {
    return {
      done: false,
    };
  }

  getSpec(): MachineSpec {
    return write(this.channel);
  }

  isCompleted(state: any): boolean {
    return state.done;
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.done) return { result: { kind: "done" }, state };
    return {
      result: { kind: "write", channel: this.channel, value: this.value },
      state: {
        done: true,
      },
    };
  }
}

export class DiscardMachine implements MachineInstance {
  constructor(private channel: string[]) {}

  createState(): any {
    return {
      done: false,
      val: undefined,
    };
  }

  getSpec(): MachineSpec {
    return read(this.channel);
  }

  isCompleted(state: any): boolean {
    return state.done;
  }

  getValue(state: any): any {
    return state.val;
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.done) return { result: { kind: "done" }, state };
    if (!action || !channelsEqual(action.channel, this.channel)) {
      return { result: { kind: "waiting" }, state };
    }
    return {
      result: { kind: "read", channel: this.channel, value: action.value },
      state: {
        done: true,
        val: action.value,
      },
    };
  }
}

export class LoopMachine implements MachineInstance {
  constructor(private factory: () => MachineInstance) {}

  createState(): any {
    const sub = this.factory();
    return {
      sub,
      subState: sub.createState(),
    };
  }

  getSpec(): MachineSpec {
    return loop(this.factory().getSpec());
  }

  isCompleted(state: any): boolean {
    return false;
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    let sub = state.sub;
    let subState = state.subState;
    if (sub.isCompleted(subState)) {
      sub = this.factory();
      subState = sub.createState();
    }
    const { result, state: nextSubState } = sub.step(subState, action);
    return {
      result,
      state: {
        ...state,
        sub,
        subState: nextSubState,
      },
    };
  }
}

export class DupMachine implements MachineInstance {
  constructor(
    private inChannel: string[],
    private outKeys: string[],
  ) {}

  createState(): any {
    return {
      state: "waiting",
      remainingWrites: [...this.outKeys],
      val: undefined,
    };
  }

  getSpec(): MachineSpec {
    const concurrentWrites = concurrent(
      Object.fromEntries(this.outKeys.map((key) => [key, write([])])),
    );
    return sequence(read(this.inChannel), concurrentWrites);
  }

  isCompleted(state: any): boolean {
    return state.state === "done";
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.state === "waiting") {
      if (!action || !channelsEqual(action.channel, this.inChannel)) {
        return { result: { kind: "waiting" }, state };
      }
      return {
        result: { kind: "read", channel: this.inChannel, value: action.value },
        state: {
          ...state,
          val: action.value,
          state: "ready",
        },
      };
    }

    if (state.state === "ready") {
      if (state.remainingWrites.length > 0) {
        const nextKey = state.remainingWrites[0];
        const nextRemaining = state.remainingWrites.slice(1);
        return {
          result: { kind: "write", channel: [nextKey], value: state.val },
          state: {
            ...state,
            remainingWrites: nextRemaining,
            state: nextRemaining.length === 0 ? "done" : "ready",
          },
        };
      }
      return {
        result: { kind: "done" },
        state: {
          ...state,
          state: "done",
        },
      };
    }

    return { result: { kind: "done" }, state };
  }
}

export class ChoiceMachine implements MachineInstance {
  private machines: Record<string, MachineInstance>;

  constructor(machines: Record<string, MachineInstance>) {
    this.machines = machines;
  }

  createState(): any {
    const states: Record<string, any> = {};
    for (const [key, sub] of Object.entries(this.machines)) {
      states[key] = sub.createState();
    }
    return {
      selected: undefined,
      states,
    };
  }

  getSpec(): MachineSpec {
    const subSpecs: MachineSpec[] = [];
    for (const sub of Object.values(this.machines)) {
      subSpecs.push(sub.getSpec());
    }
    return {
      kind: "choice",
      choices: subSpecs,
    };
  }

  isCompleted(state: any): boolean {
    if (state.selected === undefined) {
      return false;
    }
    return this.machines[state.selected].isCompleted(
      state.states[state.selected],
    );
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (state.selected !== undefined) {
      const sub = this.machines[state.selected];
      const subState = state.states[state.selected];
      const { result, state: nextSubState } = sub.step(subState, action);
      const nextStates = {
        ...state.states,
        [state.selected]: nextSubState,
      };
      return {
        result,
        state: {
          ...state,
          states: nextStates,
        },
      };
    }

    if (action) {
      // Find which sub-machine can accept this read action
      for (const [key, sub] of Object.entries(this.machines)) {
        const subState = state.states[key];
        const next = transition(sub.getSpec(), {
          kind: "read",
          channel: action.channel,
        });
        if (next !== null) {
          const { result, state: nextSubState } = sub.step(subState, action);
          const nextStates = {
            ...state.states,
            [key]: nextSubState,
          };
          return {
            result,
            state: {
              ...state,
              selected: key,
              states: nextStates,
            },
          };
        }
      }
      return { result: { kind: "waiting" }, state };
    }

    // Check if any sub-machine wants to write
    const nextStates = { ...state.states };
    for (const [key, sub] of Object.entries(this.machines)) {
      const subState = nextStates[key];
      const { result, state: nextSubState } = sub.step(subState);
      nextStates[key] = nextSubState;
      if (result.kind === "write") {
        return {
          result,
          state: {
            ...state,
            selected: key,
            states: nextStates,
          },
        };
      }
    }

    return {
      result: { kind: "waiting" },
      state: { ...state, states: nextStates },
    };
  }
}

export class PrefixMachine implements MachineInstance {
  private inner: MachineInstance;
  private prefixPath: string[];

  constructor(prefixPath: string[], inner: MachineInstance) {
    this.inner = inner;
    this.prefixPath = prefixPath;
  }

  createState(): any {
    return {
      innerState: this.inner.createState(),
    };
  }

  getSpec(): MachineSpec {
    return {
      kind: "prefix",
      prefix: this.prefixPath,
      inner: this.inner.getSpec(),
    };
  }

  isCompleted(state: any): boolean {
    return this.inner.isCompleted(state.innerState);
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action) {
      const suffix = getSuffix(action.channel, this.prefixPath);
      if (suffix === null) {
        return { result: { kind: "waiting" }, state };
      }
      const { result, state: nextInnerState } = this.inner.step(
        state.innerState,
        { channel: suffix, value: action.value },
      );
      return {
        result: this.wrapResult(result),
        state: { ...state, innerState: nextInnerState },
      };
    }

    const { result, state: nextInnerState } = this.inner.step(state.innerState);
    return {
      result: this.wrapResult(result),
      state: { ...state, innerState: nextInnerState },
    };
  }

  private wrapResult(res: StepResult): StepResult {
    if (res.kind === "read" || res.kind === "write") {
      return {
        ...res,
        channel: [...this.prefixPath, ...res.channel],
      };
    }
    return res;
  }
}

export class RenameMachine implements MachineInstance {
  private inner: MachineInstance;
  private mapping: Array<[string[], string[]]>;

  constructor(inner: MachineInstance, mapping: Array<[string[], string[]]>) {
    this.inner = inner;
    this.mapping = mapping;
  }

  createState(): any {
    return {
      innerState: this.inner.createState(),
    };
  }

  getSpec(): MachineSpec {
    return {
      kind: "rename",
      mapping: this.mapping,
      inner: this.inner.getSpec(),
    };
  }

  isCompleted(state: any): boolean {
    return this.inner.isCompleted(state.innerState);
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action) {
      const mappedChan = this.translateOuterToInner(action.channel);
      if (mappedChan === null) {
        return { result: { kind: "waiting" }, state };
      }
      const { result, state: nextInnerState } = this.inner.step(
        state.innerState,
        { channel: mappedChan, value: action.value },
      );
      return {
        result: this.wrapResult(result),
        state: { ...state, innerState: nextInnerState },
      };
    }

    const { result, state: nextInnerState } = this.inner.step(state.innerState);
    return {
      result: this.wrapResult(result),
      state: { ...state, innerState: nextInnerState },
    };
  }

  private translateOuterToInner(chan: string[]): string[] | null {
    for (const [from, to] of this.mapping) {
      if (getSuffix(chan, from) !== null && !channelsEqual(from, to)) {
        return null;
      }
    }
    for (const [from, to] of this.mapping) {
      const suffix = getSuffix(chan, to);
      if (suffix !== null) {
        return [...from, ...suffix];
      }
    }
    return chan;
  }

  private wrapResult(res: StepResult): StepResult {
    if (res.kind === "read" || res.kind === "write") {
      return {
        ...res,
        channel: this.translateInnerToOuter(res.channel),
      };
    }
    return res;
  }

  private translateInnerToOuter(chan: string[]): string[] {
    for (const [from, to] of this.mapping) {
      const suffix = getSuffix(chan, from);
      if (suffix !== null) {
        return [...to, ...suffix];
      }
    }
    return chan;
  }
}

export class IndexedMachine implements MachineInstance {
  private factory: () => MachineInstance;
  private active: Record<string, MachineInstance>;
  private templateSpec: MachineSpec;

  constructor(
    factory: () => MachineInstance,
    active: Record<string, MachineInstance> = {},
  ) {
    this.factory = factory;
    this.active = active;
    const dummy = factory();
    this.templateSpec = dummy.getSpec();
  }

  createState(): any {
    const activeStates: Record<string, any> = {};
    for (const [key, sub] of Object.entries(this.active)) {
      activeStates[key] = sub.createState();
    }
    return {
      activeStates,
    };
  }

  getSpec(): MachineSpec {
    const activeSpecs: Record<string, MachineSpec> = {};
    for (const [key, sub] of Object.entries(this.active)) {
      activeSpecs[key] = sub.getSpec();
    }
    return {
      kind: "indexed",
      inner: this.templateSpec,
      active: activeSpecs,
      activated: Object.keys(this.active).length > 0,
      then: sequence(),
    };
  }

  isCompleted(state: any): boolean {
    return Object.entries(state.activeStates).every(([key, subState]) => {
      const sub = this.factory();
      return sub.isCompleted(subState);
    });
  }

  step(
    state: any,
    action?: { channel: string[]; value?: any },
  ): { result: StepResult; state: any } {
    if (action && action.channel.length > 0) {
      const index = action.channel[0];
      const suffix = action.channel.slice(1);

      const sub = this.factory();
      let subState = state.activeStates[index];
      if (!subState) {
        subState = sub.createState();
      }

      const { result, state: nextSubState } = sub.step(subState, {
        channel: suffix,
        value: action.value,
      });

      const nextActiveStates = { ...state.activeStates };
      if (sub.isCompleted(nextSubState)) {
        delete nextActiveStates[index];
      } else {
        nextActiveStates[index] = nextSubState;
      }

      const nextState = {
        ...state,
        activeStates: nextActiveStates,
      };

      if (result.kind === "read" || result.kind === "write") {
        return {
          result: {
            ...result,
            channel: [index, ...result.channel],
          },
          state: nextState,
        };
      }
      return { result, state: nextState };
    }

    const nextActiveStates = { ...state.activeStates };
    for (const [key, subState] of Object.entries(state.activeStates)) {
      const sub = this.factory();
      const { result, state: nextSubState } = sub.step(subState);
      nextActiveStates[key] = nextSubState;
      if (result.kind === "write") {
        if (sub.isCompleted(nextSubState)) {
          delete nextActiveStates[key];
        }
        return {
          result: {
            kind: "write",
            channel: [key, ...result.channel],
            value: result.value,
          },
          state: {
            ...state,
            activeStates: nextActiveStates,
          },
        };
      }
    }

    return {
      result: { kind: "waiting" },
      state: { ...state, activeStates: nextActiveStates },
    };
  }
}

export function findStateForMachine(
  machine: MachineInstance,
  state: any,
  target: MachineInstance,
): any | null {
  if (machine === target) {
    return state;
  }
  if (machine instanceof TraceMachine) {
    return findStateForMachine(
      (machine as any).inner,
      state.innerState,
      target,
    );
  }
  if (machine instanceof RenameMachine) {
    return findStateForMachine(
      (machine as any).inner,
      state.innerState,
      target,
    );
  }
  if (machine instanceof ConcurrentMachine) {
    for (const [key, sub] of Object.entries((machine as any).machines)) {
      const found = findStateForMachine(
        sub as MachineInstance,
        state.states[key],
        target,
      );
      if (found !== null) return found;
    }
  }
  if (machine instanceof SequenceMachine) {
    for (let i = 0; i < (machine as any).machines.length; i++) {
      const found = findStateForMachine(
        (machine as any).machines[i],
        state.states[i],
        target,
      );
      if (found !== null) return found;
    }
  }
  return null;
}
