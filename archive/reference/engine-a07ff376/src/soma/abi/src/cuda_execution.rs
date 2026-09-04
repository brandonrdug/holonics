//! Word-exact CUDA transport for one live event consequence.

use body::manifold::{
    face_packed_word, node_packed_word, packed_face_is_canonical, packed_node_is_canonical,
    unpack_face, unpack_node, AtomEvent, Face, Landing, Pathing, Perception, FACE_WORDS,
    NODE_WORDS,
};
use body::medium::{RegionalForm, FORM_WORDS};
use body::num::{self, COG_WORDS};

use crate::conduct::EventContact;

#[inline]
const fn put_u64(words: &mut [u32], at: usize, value: u64) {
    words[at] = value as u32;
    words[at + 1] = (value >> 32) as u32;
}

#[inline]
const fn get_u64(words: &[u32], at: usize) -> u64 {
    words[at] as u64 | ((words[at + 1] as u64) << 32)
}

#[inline]
const fn put_i64(words: &mut [u32], at: usize, value: i64) {
    put_u64(words, at, value as u64)
}

#[inline]
const fn get_i64(words: &[u32], at: usize) -> i64 {
    get_u64(words, at) as i64
}

fn pack_face(face: Face, words: &mut [u32], at: usize) {
    let mut word = 0;
    while word < FACE_WORDS {
        words[at + word] = face_packed_word(face, word);
        word += 1;
    }
}

fn pack_node(node: body::manifold::Node, words: &mut [u32], at: usize) {
    let mut word = 0;
    while word < NODE_WORDS {
        words[at + word] = node_packed_word(node, word);
        word += 1;
    }
}

fn pack_cog(cog: body::num::Cog, words: &mut [u32], at: usize) {
    let mut word = 0;
    while word < COG_WORDS {
        words[at + word] = num::cog_packed_word(cog, word);
        word += 1;
    }
}

const CONTACT_EVENT: usize = 0;
const CONTACT_ATOM_OFFSET: usize = CONTACT_EVENT + 2;
const CONTACT_ATOMS: usize = CONTACT_ATOM_OFFSET + 2;
const CONTACT_ACTION: usize = CONTACT_ATOMS + 2;
const CONTACT_FOLD_PRESENT: usize = CONTACT_ACTION + COG_WORDS;
const CONTACT_FOLD: usize = CONTACT_FOLD_PRESENT + 1;
const CONTACT_PERCEPTION_PRESENT: usize = CONTACT_FOLD + NODE_WORDS;
const CONTACT_PERCEPTION_CELL_PRESENT: usize = CONTACT_PERCEPTION_PRESENT + 1;
const CONTACT_PERCEPTION_CELL: usize = CONTACT_PERCEPTION_CELL_PRESENT + 1;
const CONTACT_PERCEPTION_FACE: usize = CONTACT_PERCEPTION_CELL + 1;
const CONTACT_PERCEPTION_MEETING: usize = CONTACT_PERCEPTION_FACE + FACE_WORDS;
const CONTACT_PERCEPTION_FOUNDS: usize = CONTACT_PERCEPTION_MEETING + 4;
const CONTACT_PERCEPTION_FACES: usize = CONTACT_PERCEPTION_FOUNDS + 1;
const CONTACT_PERCEPTION_FACES_FOUNDED: usize = CONTACT_PERCEPTION_FACES + 1;
const CONTACT_PERCEPTION_THOUGHT_COMPLETED: usize = CONTACT_PERCEPTION_FACES_FOUNDED + 1;
const CONTACT_PERCEPTION_THOUGHT_DEPOSITED: usize = CONTACT_PERCEPTION_THOUGHT_COMPLETED + 1;
const CONTACT_PERCEPTION_CLIMBED: usize = CONTACT_PERCEPTION_THOUGHT_DEPOSITED + 1;
const CONTACT_STEP_PRESENT: usize = CONTACT_PERCEPTION_CLIMBED + 1;
const CONTACT_STEP_GRIP_PRESENT: usize = CONTACT_STEP_PRESENT + 1;
const CONTACT_STEP_GRIP: usize = CONTACT_STEP_GRIP_PRESENT + 1;
const CONTACT_STEP_FORM: usize = CONTACT_STEP_GRIP + 1;
const CONTACT_STEP_CUT: usize = CONTACT_STEP_FORM + FORM_WORDS;
const CONTACT_STEP_STEPPED: usize = CONTACT_STEP_CUT + 1;
const CONTACT_STEP_ROTOR: usize = CONTACT_STEP_STEPPED + 1;
const CONTACT_STEP_BRICK_PRESENT: usize = CONTACT_STEP_ROTOR + 2 * COG_WORDS;
const CONTACT_STEP_BRICK: usize = CONTACT_STEP_BRICK_PRESENT + 1;
pub const EVENT_CONTACT_WORDS: usize = CONTACT_STEP_BRICK + NODE_WORDS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct EventContactRow(pub [u32; EVENT_CONTACT_WORDS]);

impl EventContactRow {
    pub fn new(contact: EventContact) -> Self {
        let mut words = [0u32; EVENT_CONTACT_WORDS];
        put_u64(&mut words, CONTACT_EVENT, contact.event);
        put_u64(&mut words, CONTACT_ATOM_OFFSET, contact.atom_offset);
        put_u64(&mut words, CONTACT_ATOMS, contact.atoms);
        pack_cog(contact.action, &mut words, CONTACT_ACTION);
        if let Some(fold) = contact.consequence.fold {
            words[CONTACT_FOLD_PRESENT] = 1;
            pack_node(fold, &mut words, CONTACT_FOLD);
        }
        if let Some(perception) = contact.consequence.perception {
            words[CONTACT_PERCEPTION_PRESENT] = 1;
            if let Some(cell) = perception.landing.cell {
                words[CONTACT_PERCEPTION_CELL_PRESENT] = 1;
                words[CONTACT_PERCEPTION_CELL] = cell;
            }
            pack_face(perception.landing.face, &mut words, CONTACT_PERCEPTION_FACE);
            put_i64(
                &mut words,
                CONTACT_PERCEPTION_MEETING,
                perception.landing.meeting_ratio.0,
            );
            put_i64(
                &mut words,
                CONTACT_PERCEPTION_MEETING + 2,
                perception.landing.meeting_ratio.1,
            );
            words[CONTACT_PERCEPTION_FOUNDS] = perception.landing.founds as u32;
            words[CONTACT_PERCEPTION_FACES] = perception.faces;
            words[CONTACT_PERCEPTION_FACES_FOUNDED] = perception.faces_founded;
            words[CONTACT_PERCEPTION_THOUGHT_COMPLETED] = perception.thought_completed as u32;
            words[CONTACT_PERCEPTION_THOUGHT_DEPOSITED] = perception.thought_deposited as u32;
            words[CONTACT_PERCEPTION_CLIMBED] = perception.climbed;
        }
        if let Some(step) = contact.consequence.step {
            words[CONTACT_STEP_PRESENT] = 1;
            if let Some(grip) = step.grip {
                words[CONTACT_STEP_GRIP_PRESENT] = 1;
                words[CONTACT_STEP_GRIP] = grip;
            }
            step.regional_form.pack(&mut words, CONTACT_STEP_FORM);
            words[CONTACT_STEP_CUT] = step.cut as u32;
            words[CONTACT_STEP_STEPPED] = step.stepped as u32;
            pack_cog(step.meeting_rotor.0, &mut words, CONTACT_STEP_ROTOR);
            pack_cog(
                step.meeting_rotor.1,
                &mut words,
                CONTACT_STEP_ROTOR + COG_WORDS,
            );
            if let Some(brick) = step.brick {
                words[CONTACT_STEP_BRICK_PRESENT] = 1;
                pack_node(brick, &mut words, CONTACT_STEP_BRICK);
            }
        }
        Self(words)
    }

    pub fn contact(self) -> Option<EventContact> {
        let words = &self.0;
        if !num::packed_cog_is_canonical(words, CONTACT_ACTION)
            || words[CONTACT_FOLD_PRESENT] > 1
            || words[CONTACT_PERCEPTION_PRESENT] > 1
            || words[CONTACT_STEP_PRESENT] > 1
        {
            return None;
        }
        let fold = if words[CONTACT_FOLD_PRESENT] == 1 {
            packed_node_is_canonical(words, CONTACT_FOLD).then(|| unpack_node(words, CONTACT_FOLD))
        } else {
            if words[CONTACT_FOLD..CONTACT_FOLD + NODE_WORDS]
                .iter()
                .any(|word| *word != 0)
            {
                return None;
            }
            None
        };
        if words[CONTACT_FOLD_PRESENT] == 1 && fold.is_none() {
            return None;
        }

        let perception = if words[CONTACT_PERCEPTION_PRESENT] == 1 {
            if words[CONTACT_PERCEPTION_CELL_PRESENT] > 1
                || words[CONTACT_PERCEPTION_FOUNDS] > 1
                || words[CONTACT_PERCEPTION_THOUGHT_COMPLETED] > 1
                || words[CONTACT_PERCEPTION_THOUGHT_DEPOSITED] > 1
                || !packed_face_is_canonical(words, CONTACT_PERCEPTION_FACE)
            {
                return None;
            }
            Some(Perception {
                landing: Landing {
                    cell: (words[CONTACT_PERCEPTION_CELL_PRESENT] == 1)
                        .then_some(words[CONTACT_PERCEPTION_CELL]),
                    face: unpack_face(words, CONTACT_PERCEPTION_FACE),
                    meeting_ratio: (
                        get_i64(words, CONTACT_PERCEPTION_MEETING),
                        get_i64(words, CONTACT_PERCEPTION_MEETING + 2),
                    ),
                    founds: words[CONTACT_PERCEPTION_FOUNDS] == 1,
                },
                faces: words[CONTACT_PERCEPTION_FACES],
                faces_founded: words[CONTACT_PERCEPTION_FACES_FOUNDED],
                thought_completed: words[CONTACT_PERCEPTION_THOUGHT_COMPLETED] == 1,
                thought_deposited: words[CONTACT_PERCEPTION_THOUGHT_DEPOSITED] == 1,
                climbed: words[CONTACT_PERCEPTION_CLIMBED],
            })
        } else {
            if words[CONTACT_PERCEPTION_CELL_PRESENT..CONTACT_STEP_PRESENT]
                .iter()
                .any(|word| *word != 0)
            {
                return None;
            }
            None
        };

        let step = if words[CONTACT_STEP_PRESENT] == 1 {
            if words[CONTACT_STEP_GRIP_PRESENT] > 1
                || words[CONTACT_STEP_CUT] > 1
                || words[CONTACT_STEP_STEPPED] > 1
                || words[CONTACT_STEP_BRICK_PRESENT] > 1
                || RegionalForm::unpack_compact_checked(words, CONTACT_STEP_FORM).is_err()
                || !num::packed_cog_is_canonical(words, CONTACT_STEP_ROTOR)
                || !num::packed_cog_is_canonical(words, CONTACT_STEP_ROTOR + COG_WORDS)
            {
                return None;
            }
            let brick = if words[CONTACT_STEP_BRICK_PRESENT] == 1 {
                packed_node_is_canonical(words, CONTACT_STEP_BRICK)
                    .then(|| unpack_node(words, CONTACT_STEP_BRICK))
            } else {
                if words[CONTACT_STEP_BRICK..CONTACT_STEP_BRICK + NODE_WORDS]
                    .iter()
                    .any(|word| *word != 0)
                {
                    return None;
                }
                None
            };
            if words[CONTACT_STEP_BRICK_PRESENT] == 1 && brick.is_none() {
                return None;
            }
            Some(Pathing {
                grip: (words[CONTACT_STEP_GRIP_PRESENT] == 1).then_some(words[CONTACT_STEP_GRIP]),
                regional_form: RegionalForm::unpack_compact_checked(words, CONTACT_STEP_FORM)
                    .ok()?,
                cut: words[CONTACT_STEP_CUT] == 1,
                stepped: words[CONTACT_STEP_STEPPED] == 1,
                meeting_rotor: (
                    num::read_cog(words, CONTACT_STEP_ROTOR),
                    num::read_cog(words, CONTACT_STEP_ROTOR + COG_WORDS),
                ),
                brick,
            })
        } else {
            if words[CONTACT_STEP_GRIP_PRESENT..EVENT_CONTACT_WORDS]
                .iter()
                .any(|word| *word != 0)
            {
                return None;
            }
            None
        };

        Some(EventContact {
            event: get_u64(words, CONTACT_EVENT),
            atom_offset: get_u64(words, CONTACT_ATOM_OFFSET),
            atoms: get_u64(words, CONTACT_ATOMS),
            action: num::read_cog(words, CONTACT_ACTION),
            consequence: AtomEvent {
                fold,
                perception,
                step,
            },
        })
    }

    pub const fn words(self) -> [u32; EVENT_CONTACT_WORDS] {
        self.0
    }
}
