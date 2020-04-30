# -*- coding: utf-8 -*-
"""
Created on Wed Apr  8 11:47:14 2020

@author: colin
"""

import CPolys

CPolys_dict = {}

for poly in CPolys.allConwayPolynomials:
    if poly[0] not in  CPolys_dict.keys():
        CPolys_dict[poly[0]] = {}
    CPolys_dict[poly[0]][poly[1]] = poly[2]
    
    
import pickle

with open('Cpolys_dict.txt', 'wb') as handle:
  pickle.dump(CPolys_dict, handle)
  
  CPolys_dict[5][2]
