/*
 * synthesize.h
 *
 *  Created on: Oct 29, 2020
 *      Author: nbingham
 */

#pragma once

#include <common/standard.h>

#include <ucs/variable.h>
#include <hse/graph.h>
#include <hse/state.h>

#include <prs/production_rule.h>

prs::production_rule_set hse_to_prs(const hse::graph &g);
boolean::cover strengthen(petri::iterator firing);

