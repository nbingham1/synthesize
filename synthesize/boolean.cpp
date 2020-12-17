/*
 * boolean.cpp
 *
 *  Created on: Oct 29, 2020
 *      Author: nbingham
 */

#include "boolean.h"

boolean::unsigned_int decompose_hfactor(boolean::unsigned_int c, int w, map<boolean::cube, int> &factors, ucs::variable_set &vars, vector<int> hide)
{
	if (c.max_width() >= w and c.depth() > 1) {
		boolean::cube common = c.supercube();
		common.hide(hide);
		if (common.width() < w)
		{
			boolean::unsigned_int c_left, c_right;
			boolean::unsigned_int left_result, right_result;
			c.partition(c_left, c_right);

			left_result = decompose_hfactor(c_left, w, factors, vars, hide);
			right_result = decompose_hfactor(c_right, w, factors, vars, hide);
			return left_result | right_result;
		}
		else
		{
			c.cofactor(common);
			int index = -1;
			map<boolean::cube, int>::iterator loc = factors.find(common);
			if (loc == factors.end()) {
				index = vars.define(ucs::variable());
				vars.nodes[index].name.push_back(ucs::instance("f", {(int)factors.size()}));
				factors.insert(pair<boolean::cube, int>(common, index));
			} else {
				index = loc->second;
			}

			boolean::unsigned_int result = decompose_hfactor(c, w, factors, vars, hide);
			for (int i = 0; i < (int)result.bits.size(); i++) {
				result.bits[i] &= boolean::cube(index, 1);
			}
			return result;
		}
	}

	return c;
}

boolean::unsigned_int decompose_xfactor(boolean::unsigned_int c, int w, map<boolean::cube, int> &factors, ucs::variable_set &vars, vector<int> hide)
{
	if (c.max_width() >= w and c.depth() > 1) {
		boolean::unsigned_int nc = ~c;
		boolean::cube common = c.supercube();
		boolean::cube ncommon = nc.supercube();
		common.hide(hide);
		ncommon.hide(hide);
		int cw = common.width(), ncw = ncommon.width();

		if (cw < w and ncw < w) {
			boolean::unsigned_int c_left, c_right, nc_left, nc_right;
			boolean::unsigned_int result, left_result, right_result;
			float c_weight, nc_weight;
			
			c_weight = c.partition(c_left, c_right);
			nc_weight = nc.partition(nc_left, nc_right);

			if (c_weight <= nc_weight)
			{
				left_result = decompose_xfactor(c_left, w, factors, vars, hide);
				right_result = decompose_xfactor(c_right, w, factors, vars, hide);
				result = left_result | right_result;
			}
			else if (nc_weight < c_weight)
			{
				left_result = decompose_xfactor(nc_left, w, factors, vars, hide);
				right_result = decompose_xfactor(nc_right, w, factors, vars, hide);
				result = left_result | right_result;
				// TODO We're getting stuck here...
				result = ~result;
			}
			return result;
		} else if (cw >= ncw) {
			c.cofactor(common);

			map<boolean::cube, int>::iterator loc = factors.find(common);
			int index = -1;
			if (loc == factors.end()) {
				index = vars.define(ucs::variable());
				vars.nodes[index].name.push_back(ucs::instance("f", {(int)factors.size()}));
				factors.insert(pair<boolean::cube, int>(common, index));
			} else {
				index = loc->second;
			}
		
			boolean::unsigned_int result = decompose_xfactor(c, w, factors, vars, hide);
			for (int i = 0; i < (int)result.bits.size(); i++) {
				result.bits[i] &= boolean::cube(index, 1);
			}
			return result;
		} else if (ncw > cw) {
			nc.cofactor(ncommon);

			map<boolean::cube, int>::iterator loc = factors.find(ncommon);
			int index = -1;
			if (loc == factors.end()) {
				index = vars.define(ucs::variable());
				vars.nodes[index].name.push_back(ucs::instance("f", {(int)factors.size()}));
				factors.insert(pair<boolean::cube, int>(ncommon, index));
			} else {
				index = loc->second;
			}
			
			boolean::unsigned_int result = decompose_xfactor(nc, w, factors, vars, hide);
			for (int i = 0; i < (int)result.bits.size(); i++) {
				result.bits[i] &= boolean::cube(index, 1);
			}
			return ~result;
		}
	}

	return c;
}

