# ELASTIC MEDIUM 01 · THE WORLD CARRIES THE STROKE

**GRADE: FAILED APPARATUS · EXACT 16-CELL GAZE ALIAS · 55,296 DARK ROWS · ZERO STEP · EXACT
REPEAT · NO WORLD EVOLUTION · NO SOMA MECHANISM CHANGE**

The first run exposed that every gaze displacement was divisible by the visible weave's 16-cell
period. All 9,216 contact worldlines therefore stayed unchanged across six events. Broad/repeat
radiation and successor bodies are exact, but §XLV supplies no contact without STEP. No simulated
world change was fabricated. ELASTIC MEDIUM 02 preserves this record and corrects only the gaze.

This is the first post-`FORMULA §XLVI` construction outside the editor/text material species. The
same byte-identical broad/repeat conversation bodies receive a visible exact simulated medium
through the unchanged gaze eye. Their native radiation acts through the ratified pressure contact
face; the changed medium then returns through the same eye.

## The concrete world species

The world is a bounded 192×192 woven torus. Its 96×96 aperture follows one six-event closed gaze
route. Horizontal and vertical displacement channels carry the exact integer recurrence

```text
x_next[x,y] = x_current[x-1,y] + x_current[x+1,y]
              - x_previous[x,y] + x_forcing[x,y]

y_next[x,y] = y_current[x,y-1] + y_current[x,y+1]
              - y_previous[x,y] + y_forcing[x,y].
```

This is a chosen world-side simulation law, not Soma law. It has no floats, clipping, damping,
randomness, scheduler, or hidden iteration. One emitted gaze-event contact configuration causes one
medium turn. Every STEP contributes one inward quantum to both woven directions at its actual world
contact. CUT⊕BRICK also leaves one persistent endpoint count. Co-present contacts at one cell add as
that medium's physical forcing; this is not selection, voting, scoring, or a motor command.

The update is exactly invertible from its retained forcing: the new previous sheet is the old
current sheet, so the prior sheet reconstructs directly. The observer verifies the full causal
inverse. Exact state remains world/listener-side. The P5 field is a declared visual compression and
refuses rather than clips if its bounded chart cannot represent the state.

## Controls and owed reads

- broad and repeat begin from byte-identical bodies and the exact same resting field;
- contact radiation, forcing, complete world state, rendered field, and action successor must
  repeat exactly;
- reversing the declared medium turns with the retained contact configurations must restore the
  initial state exactly;
- one fixed action successor receives the changed and unchanged field through the same gaze;
- changed versus unchanged must be read across complete plural radiation, while broad/repeat stays
  exact through the returned successor body.

No material state is smuggled into Soma. The eye presents the visible field only. Complete state,
contacts, forcing, and causal history remain beside the construction as the listener's record.

From `src/soma/`:

```bash
python3 -B observations/elastic-medium-01/build_world.py
./target/release/life --eye-card observations/elastic-medium-01/generated/initial.eye
bash observations/elastic-medium-01/run_action_cuda.sh
python3 -B observations/elastic-medium-01/evolve_world.py
python3 -B observations/elastic-medium-01/verify_world.py
bash observations/elastic-medium-01/gate_cuda.sh
bash observations/elastic-medium-01/run_return_cuda.sh
python3 -B observations/elastic-medium-01/read_results.py
```

Every generated state, report, compact read, and sleeping body is create-new.
