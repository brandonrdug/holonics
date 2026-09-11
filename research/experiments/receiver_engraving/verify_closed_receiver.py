"""Exact image checks for the outward-boundary visibility option and safe depth rejection."""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util,sys,subprocess
import woven_ecology as w
r=w.r;ROOT=w.ROOT

def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);return module

def signature(scene):
    return {(m['kind'],tuple(sorted(tuple(p) for p in m['points'])),tuple(m['rgb']),m['width']) for m in scene['marks']}

def main():
    old=ROOT/'.local/scratch/stress-knot-review/receiver-before-woven.py'
    old.write_text(subprocess.check_output(['git','show','703d7504:research/papers/source/packages/holonic-receiver/compile.py'],cwd=ROOT,text=True))
    before=load(old,'receiver_before_woven')
    vertices=[(0,0,0),(1,0,0),(0,1,0),(0,0,1)]
    faces=[(0,2,1),(0,1,3),(0,3,2),(1,2,3)]
    currents=[((Q(i+1,3),Q(2-i,5)),(0,0),(0,0)) for i in range(4)]
    views=[{},dict(right=(Q(1),Q(1),Q(0)),up=(Q(0),Q(1),Q(1)),view=(Q(1),Q(0),Q(1)),distance=Q(8),focal=Q(4),perspective=True)]
    for opts in views:
        oldscene=before.compile_scene(vertices,faces,currents=currents,receiver=before.Receiver(**opts),step=Q(1,8))
        normal=r.compile_scene(vertices,faces,currents=currents,receiver=r.Receiver(**opts),step=Q(1,8))
        outward=r.compile_scene(vertices,faces,currents=currents,receiver=r.Receiver(**opts),step=Q(1,8),closed_outward=True)
        assert signature(oldscene)==signature(normal)
        assert signature(normal)==signature(outward)
        assert normal['source_packet']==outward['source_packet']
        assert outward['meta']['back_faces']
    print('Outward-boundary and depth/AABB rejection match prior exact images; orthographic and skew pinhole receivers retain the complete source packet.')

if __name__=='__main__':main()
