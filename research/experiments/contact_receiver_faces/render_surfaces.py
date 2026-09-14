"""Display projection only. Collision membership and area vectors come from exact.py/surfaces.py data.
No plotting coordinate decides which face participates.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,sys
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
HERE=Path(__file__).parent;ROOT=HERE.parents[2]
OUT=ROOT/'research/papers/source/papers/elementary-holon-generation/figures'
sys.path.insert(0,str(ROOT/'research/experiments/intrinsic_holonic_flow'))
from flow import advect

def main():
    receipt=json.loads((HERE/'surface_faces.json').read_text())
    plt.rcParams.update({'font.family':'DejaVu Serif','font.size':10,'svg.fonttype':'path'})
    fig=plt.figure(figsize=(11,4.2));axes=[fig.add_subplot(121,projection='3d',computed_zorder=False),fig.add_subplot(122,projection='3d',computed_zorder=False)]
    for entry,color in zip(receipt['surfaces'],['#c85940','#28719e']):
        # Exact stored source -> screen geometry is the only conversion to machine floats.
        pts=np.array([[float(Q(x)) for x in row] for row in entry['vertices']]);shown=advect(pts)
        faces=np.array(entry['faces']);patch=np.array([f['indices'] for f in entry['collision_faces']])
        for ax in axes:
            ax.add_collection3d(Poly3DCollection(shown[faces],facecolors='#d9e2e4',edgecolors='#88999d',linewidths=.08,alpha=.07,zorder=1))
            ax.add_collection3d(Poly3DCollection(shown[patch],facecolors=color,edgecolors=color,linewidths=.3,alpha=.6,zorder=3))
    for ax in axes:
        ax.view_init(elev=25,azim=-53);ax.set_axis_off();ax.set_box_aspect((1,1,1));ax.set_proj_type('persp')
    axes[0].set(xlim=(-3.5,3.5),ylim=(-3,6),zlim=(-3.5,3.5));axes[0].set_box_aspect((7,9,7),zoom=1.15)
    axes[0].set_title('Two toroidal boundary faces · exact collision groups',fontsize=12)
    axes[1].set(xlim=(-1.25,1.25),ylim=(.2,2.8),zlim=(-1.25,1.25));axes[1].set_box_aspect((1,1,1),zoom=.9)
    axes[1].set_title('Shared region · shear-bearing surface patches',fontsize=12)
    # Receiver at a participating facet, not a free-floating camera ontology.
    site=receipt['surfaces'][0]['collision_faces'][len(receipt['surfaces'][0]['collision_faces'])//2]
    material=np.array([float(Q(x)) for x in site['center']]);p=advect(material)
    n=np.array([float(Q(x)) for x in site['area_vector']])
    angle=material[0]/8;c=np.cos(angle);s=np.sin(angle)
    n=np.array([n[0]+(material[2]*n[1]-material[1]*n[2])/8,c*n[1]-s*n[2],s*n[1]+c*n[2]])
    n=n/np.linalg.norm(n)
    axes[1].quiver(*p,*(.75*n),color='black',linewidth=1.2,arrow_length_ratio=.2,zorder=8)
    axes[1].text(*(p+.8*n),'nΣ',fontsize=11,zorder=9)
    axes[1].text(*p,' R: (U, T, Σ)',fontsize=10,zorder=9)
    fig.subplots_adjust(left=0,right=1,bottom=0,top=.91,wspace=.03)
    fig.savefig(OUT/'exact-collision-surfaces.svg',bbox_inches='tight',pad_inches=.04)
    plt.close(fig)
if __name__=='__main__':main()
