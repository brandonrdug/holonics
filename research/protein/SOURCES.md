# Sources and reuse

Protein Data Bank archive data, including the Chemical Component Dictionary, are released
under [CC0 1.0 by wwPDB](https://www.wwpdb.org/about/usage-policies). Attribution identifies
the entries below. The copied CCD file is archive data; no journal article text, figure or
commercial database material is redistributed. New code and authored documentation follow
the repository's MIT OR Apache-2.0 license.

| Source | Role and exact identity |
|---|---|
| [1UBQ](https://www.rcsb.org/structure/1UBQ), [entry DOI](https://doi.org/10.2210/pdb1UBQ/pdb) | Observed ubiquitin geometry ancestry. The local ATOM-only projection had 602 records, 49653 bytes and SHA-256 `7ba62fc2b6653ab9c4bde60f4976f2fc465076266e5f24f9b6b781538918cacb`. It was a projection, not byte-identical to the full archive PDB. It is not copied into this package. The candidate sequence differs from ubiquitin. |
| [6ARU](https://www.rcsb.org/structure/6ARU), [entry DOI](https://doi.org/10.2210/pdb6ARU/pdb) | Observed EGFR target chain A. Original archive PDB: 1372383 bytes, SHA-256 `6009474a03942ad6d6b01f3145cb6f102f549290001c240b7ae1fcc0e071d5c0`. The entry contains a cetuximab Fab complex; that fact is not candidate binding evidence. The two target anchor coordinates are included in the receiving input. |
| [CCD NML](https://www.rcsb.org/ligand/NML), [source CIF](https://files.rcsb.org/ligands/download/NML.cif) | **N-METHYLACETAMIDE**, formula C3 H7 N O. [NML.cif](sources/NML.cif): 5091 bytes, SHA-256 `3508913f3a128d8182545424e2342c3319390b910fdba85171cf41ad86e28c27`. Both model and ideal coordinate charts are retained with their literal addresses and bond incidence. CCD initial date 2006-10-27, modification date 2024-09-27; model database code 2NMV. Both coordinate-details fields are `?`; no experimentally observed H or numerical experimental error bound is asserted. NMA is not this component and is not admitted. |

The 1UBQ primary citation is Vijay-Kumar S, Bugg CE and Cook WJ (1987),
*Structure of ubiquitin refined at 1.8 Å resolution*, Journal of Molecular Biology,
[DOI 10.1016/0022-2836(87)90679-6](https://doi.org/10.1016/0022-2836(87)90679-6).
The title's precision describes its source; it supplies no error bound for these substituted
candidate charts.

The heavy source parent's scientific receipt identity is SHA-256
`4b6db679bda76efd474ba642198cbd5ca88411d6b6f8fac0c40e2fa53951636c`.
Its native producer is outside this package. Source uncertainty and transfer uncertainty
remain explicit unknowns. Exact enclosure endpoints describe arithmetic, not physiological
population, measured binding or validated folding.
