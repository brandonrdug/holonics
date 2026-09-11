#import "/packages/holonic-engraving/lib.typ": engrave
#let scenes=json("/papers/hnn-information-chemistry/receiver-scenes.json")
#set page(width:240mm,height:100mm,margin:5mm,fill:white)
#grid(columns:(1fr,1fr,1fr),gutter:4mm,
 engrave(scenes.sphere_mono,width:72mm,mode:"mono"),
 engrave(scenes.sphere_phase,width:72mm),
 engrave(scenes.torus_phase,width:72mm),
)
