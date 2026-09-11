"""Validate the source packet and publish equivalent SVG web faces.

Rational integers use strings so browser JSON does not silently round them.
Decimal mark coordinates are explicitly the exterior paint face.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,runpy,importlib.util,xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[3]
base=runpy.run_path(str(Path(__file__).with_name('build.py')));r=base['r']


def rational_tree(v):
    if isinstance(v,list):
        if len(v)==2 and all(isinstance(x,(str,int)) for x in v): return [str(x) for x in v]
        return [rational_tree(x) for x in v]
    return v


def main():
    path=ROOT/'research/papers/source/papers/hnn-information-chemistry/receiver-scenes.json'
    scenes=json.loads(path.read_text())
    for name,scene in scenes.items():
        scene['schema']='org.holonics.receiver-engraving.v1'
        source=scene['source_packet'];meta=scene['meta']
        if 'style' not in meta: meta['style']='stipple' if name=='sphere_stipple' else ('mono' if name.endswith('_mono') else 'phase')
        for key in ('vertices','currents'): source[key]=rational_tree(source[key])
        for key in ('phase','tau','aperture','hatch_step','entropy_reference','log_station_radius','decimal_coordinate_error'):
            meta[key]=rational_tree(meta[key])
        meta['receiver'].setdefault('origin',[['0','1'],['0','1'],['0','1']])
        for key,value in meta['receiver'].items(): meta['receiver'][key]=rational_tree(value)
        for row in meta.get('near_face_details',[]): row['depth_interval']=rational_tree(row['depth_interval'])
        if isinstance(meta['source'],dict) and 'generator' in meta['source']:
            meta['source']['generator']=[[[str(v) for v in cell] for cell in row] for row in meta['source']['generator']]
            meta['source']['swirl']=rational_tree(meta['source']['swirl'])
        for mark in scene['marks']:
            for key in ('visible_span','source_station_parameter'): mark[key]=rational_tree(mark[key])
            if mark['feature']:
                for key in ('level','secondary_level'):
                    if key in mark['feature']: mark['feature'][key]=rational_tree(mark['feature'][key])
            assert all(0<=c<=1 for c in mark['rgb'])
            assert all(0<=f<len(source['triangles']) for f in mark['faces'])
            if mark['kind']=='stipple': assert len(mark['points'])==1
        # Verify the actual field, not only equality of a digest or plot.
        assert isinstance(meta['source'],dict)
        description=meta['source']
        def decode_complex(v): return tuple(r.read_ratio(q) for q in v)
        if 'generator' in description:
            matrix=tuple(tuple((Q(int(v[0]),int(v[1])),Q(int(v[2]),int(v[3]))) for v in row) for row in description['generator'])
            for point,current in zip(source['vertices'],source['currents']):
                z=tuple(decode_complex(v) for v in point);u=tuple(decode_complex(v) for v in current)
                assert r.complex_matrix(matrix,z)==u
        elif description['kind']=='affine-by-region':
            for region in description['regions']:
                row=tuple(decode_complex(v) for v in region['row']);offset=decode_complex(region['offset'])
                for point,current in zip(source['vertices'][region['start']:region['end']],source['currents'][region['start']:region['end']]):
                    z=tuple(decode_complex(v) for v in point);u=tuple(decode_complex(v) for v in current)
                    value=r.ca(offset,tuple(sum(r.cm(a,b)[k] for a,b in zip(row,z)) for k in range(2)))
                    assert u==(value,(0,0),(0,0))
        elif description['kind']=='vertex-values':
            for physical,point in zip(description['carrier_vertices'],source['vertices']):
                assert tuple(r.read_ratio(v) for v in physical)==tuple(decode_complex(v)[0] for v in point)
                assert all(decode_complex(v)[1]==0 for v in point)
            assert description['carrier_faces']==source['triangles']
            for value,current in zip(description['values'],source['currents']):
                u=tuple(decode_complex(v) for v in current)
                assert u==(decode_complex(value),(0,0),(0,0))
        elif description['kind']=='cell-values':
            for i,values in enumerate(description['values']):
                for j,value in enumerate(values):
                    u=tuple(decode_complex(v) for v in source['currents'][3*i+j])
                    assert u==(decode_complex(value),(0,0),(0,0))
        else: raise ValueError('unverified source family')
        assert not meta['unresolved_near_faces']
    path.write_text(json.dumps(scenes,separators=(',',':'))+'\n')
    (ROOT/'research/experiments/receiver_engraving/receipt.json').write_text(json.dumps({k:v['meta'] for k,v in scenes.items()},indent=2)+'\n')
    spec=importlib.util.spec_from_file_location('receiver_svg',ROOT/'research/papers/source/packages/holonic-receiver/export_svg.py')
    svg=importlib.util.module_from_spec(spec);spec.loader.exec_module(svg)
    output=ROOT/'research/papers/rendered/receiver-engraving';output.mkdir(exist_ok=True)
    for name,mode in (('shorts_phase','phase'),('sphere_mono','mono'),('torus_entropy','phase'),('friction_1_2','phase'),('contact_15_16','phase')):
        scene=scenes[name];text=svg.scene_svg(scene,mode=mode)
        root=ET.fromstring(text);ns={'s':'http://www.w3.org/2000/svg'}
        marks=root.findall('.//s:polyline',ns)+root.findall('.//s:circle',ns)
        assert len(marks)==len(scene['marks'])
        assert all('data-receiver-mark' in m.attrib for m in marks)
        metadata=json.loads(root.find('s:metadata',ns).text)
        assert metadata['source_packet']==scene['source_packet']
        (output/(name+'.svg')).write_text(text)
    print('Returned: lossless rational source/current wire for',len(scenes),'scenes; five SVG faces retain the same marks and source packet.')

if __name__=='__main__':main()
