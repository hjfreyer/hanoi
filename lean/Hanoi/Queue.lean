import Hanoi.Machine

/-!
# A FIFO queue

The queue of `hana/queue.hana`: a machine that takes `pushBack` events from
producers and answers `popFront` and `awaitFront` requests, where the latter
waits for a push when the queue is empty.

Hanoi's queue has `Descending` and `Rebuilding` states in which it walks its
cons-list one cell per `tau` step to append at the back, because Hanoi has no
recursion. Lean appends to a `List` directly, so those states do not exist
here, and Hanoi's three "about to answer" states collapse into one `replying`.
-/

namespace Hanoi

/-- The envelope on a request/response channel: Hanoi's `prelude::req` and
`prelude::resp` tags. -/
inductive ReqResp (α : Type)
  | req
  | resp (a : α)
  deriving Repr, DecidableEq

namespace Queue

/-- The queue's channels, each with what it carries. -/
inductive Event (α : Type)
  /-- A producer appends `x`. -/
  | pushBack (x : α)
  /-- Take the front element; `none` when the queue is empty. -/
  | popFront (r : ReqResp (Option α))
  /-- Take the front element, waiting for a push when the queue is empty. -/
  | awaitFront (r : ReqResp (Option α))
  deriving Repr, DecidableEq

inductive State (α : Type)
  /-- Holding `items`, front first, and open for requests. -/
  | idle (items : List α)
  /-- An `awaitFront` request arrived on an empty queue; the next push answers it. -/
  | awaitingPush
  /-- About to send `reply`, and to continue as `next` once it is taken. -/
  | replying (reply : Event α) (next : State α)
  deriving Repr, DecidableEq

end Queue

/-- The queue machine over elements `α`. -/
def queue (α : Type) [DecidableEq α] : Machine (Queue.Event α) (Queue.State α) where
  init := .idle []
  accept
    | .idle _, .pushBack _ | .idle _, .popFront .req | .idle _, .awaitFront .req => true
    | .awaitingPush, .pushBack _ | .awaitingPush, .popFront .req => true
    | .replying reply _, e => e == reply
    | _, _ => false
  emit
    | .replying reply _ => some reply
    | _ => none
  step
    | .idle items, .pushBack x => some (.idle (items ++ [x]))
    | .idle items, .popFront .req =>
      some (.replying (.popFront (.resp items.head?)) (.idle items.tail))
    | .idle [], .awaitFront .req => some .awaitingPush
    | .idle (x :: rest), .awaitFront .req =>
      some (.replying (.awaitFront (.resp (some x))) (.idle rest))
    | .awaitingPush, .pushBack x =>
      some (.replying (.awaitFront (.resp (some x))) (.idle []))
    | .awaitingPush, .popFront .req =>
      some (.replying (.popFront (.resp none)) .awaitingPush)
    | .replying reply next, e => if e == reply then some next else none
    | _, _ => none
  tau _ := none
  isDone _ := false
  isReadyToFinish
    | .idle _ => true
    | _ => false

end Hanoi
