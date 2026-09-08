#!/usr/bin/env python3
"""Small exact controls for the cold enclosed-PCM observer; no native execution."""
import argparse
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import struct
import wave
import numpy as np
from compare_temporal_acoustic_application import (check_global_ball, RationalSeries,
    parse_section, section_wide_values, verify_projection, SECTION_MAGIC)


def rust_integer(value):
    sign = (value > 0) - (value < 0)
    value = abs(value)
    words = []
    while value:
        words.append(value & ((1 << 32) - 1))
        value >>= 32
    return sign, words


def rational(value):
    value = Q(value)
    return [rust_integer(value.numerator), rust_integer(value.denominator)]


def complex_value(real, imaginary):
    return {'real': rational(real), 'imaginary': rational(imaginary)}


def run(directory):
    directory.mkdir()
    controls = []
    def negative(name, action):
        try:
            action()
        except (ValueError, AssertionError, KeyError):
            controls.append({'control':name, 'expected':'refused', 'returned':'refused'})
        else:
            raise AssertionError(name + ' was accepted')

    zero = RationalSeries(np.zeros((2, 2), dtype=object), 1)
    joint = RationalSeries(np.array([[3, 0], [3, 0]], dtype=object), 4)
    negative('coordinatewise-membership-does-not-imply-global-membership',
             lambda: check_global_ball(zero, joint, Q(1)))
    check_global_ball(zero, RationalSeries(np.array([[1, 0], [0, 0]], dtype=object), 4), Q(1))
    controls.append({'control':'noncentre-compatible-global-point', 'returned':'accepted'})

    values = [-1, 1 << 63, -(1 << 63), (1 << 100) + 11]
    payload = bytearray(SECTION_MAGIC + struct.pack('<QQIIQ', 1, 2*len(values), 0, 64, 2*len(values)))
    for value in values:
        low = value & ((1 << 64) - 1)
        if low >= 1 << 63: low -= 1 << 64
        high = value >> 64
        payload.extend(struct.pack('<qqqq', low, low, high, high))
    assert section_wide_values(parse_section(payload)) == values
    controls.append({'control':'signed-wide-low-limb-and-large-high-limb', 'returned':'accepted'})

    projection = {'schema':'soma-life.native-acoustic-enclosed-temporal-pcm16.v1',
        'receiver':9, 'lineage':18, 'origin':rational(0), 'sample_step':rational(Q(1,16000)),
        'sample_rate':16000, 'gain':rational(1), 'radius':rational(Q(1,6)),
        'frames':[
            {'representative':complex_value(Q(3,2), Q(-5,3)), 'pcm':[1,-1],
             'remainder':complex_value(Q(1,2), Q(-2,3)), 'clipped':[False,False]},
            {'representative':complex_value(40000,-40000), 'pcm':[32767,-32768],
             'remainder':complex_value(7233,-7232), 'clipped':[True,True]}],
        'clipped_sample_population':2}
    wav_path = directory/'control.wav'
    with wave.open(str(wav_path), 'wb') as wav:
        wav.setparams((2,2,16000,2,'NONE','not compressed'))
        wav.writeframes(struct.pack('<hhhh',1,-1,32767,-32768))
    expected = {'raw_extent':2,'scale':6,'radius_num':1,
                'numerators':np.array([[9,-10],[240000,-240000]],dtype=object)}
    def verify(name, content):
        path = directory/(name+'.json')
        path.write_text(json.dumps(content))
        sound = {'projection':str(path), 'wav':str(wav_path), 'frames':2, 'sample_rate':16000,
            'gain':'1','channels':['real','imaginary'],'radius_native_units':'1/6',
            'clipped_coordinates':2,'wav_is_numerical_representative':True}
        return verify_projection(sound, path, expected, expected_lineage=18)
    verify('valid',projection)
    controls.append({'control':'both-quadratures-non-dyadic-clipped-PCM', 'returned':'accepted'})
    for name, mutate in [
        ('wrong-remainder', lambda p: p['frames'][0]['remainder'].update(real=rational(0))),
        ('wrong-clipping', lambda p: p['frames'][1].update(clipped=[False,True])),
        ('wrong-radius', lambda p: p.update(radius=rational(1))),
        ('wrong-clock', lambda p: p.update(sample_step=rational(Q(1,8000)))),
        ('wrong-lineage', lambda p: p.update(lineage=99)),
    ]:
        changed = copy.deepcopy(projection)
        mutate(changed)
        negative(name, lambda: verify(name,changed))
    result = {'verified':True,'scope':'cold observer controls; no native/product claim',
              'controls':controls,'native_execution':False}
    (directory/'return.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('new_directory',type=Path)
    run(parser.parse_args().new_directory)
