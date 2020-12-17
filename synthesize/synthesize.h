/*
 * synthesize.h
 *
 *  Created on: Oct 29, 2020
 *      Author: nbingham
 */

#include <common/standard.h>

#include <ucs/variable.h>
#include <hse/graph.h>
#include <hse/state.h>

#include <prs/production_rule.h>

#ifndef synthesizer_h
#define synthesizer_h

namespace hse
{

unsigned_int decompose_hfactor(unsigned_int c, int w, map<cube, int> &factors, ucs::variable_set &vars, vector<int> hide);
unsigned_int decompose_xfactor(unsigned_int c, int w, map<cube, int> &factors, ucs::variable_set &vars, vector<int> hide);

production_rule_set hse_to_prs(const graph &g);

}

#endif
