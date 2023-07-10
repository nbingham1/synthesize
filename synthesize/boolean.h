/*
 * synthesize.h
 *
 *  Created on: Oct 29, 2020
 *      Author: nbingham
 */

#pragma once

#include <common/standard.h>
#include <ucs/variable.h>
#include <boolean/unsigned_int.h>

boolean::unsigned_int decompose_hfactor(boolean::unsigned_int c, int w, map<boolean::cube, int> &factors, ucs::variable_set &vars, vector<int> hide);
boolean::unsigned_int decompose_xfactor(boolean::unsigned_int c, int w, map<boolean::cube, int> &factors, ucs::variable_set &vars, vector<int> hide);

