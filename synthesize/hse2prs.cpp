/*
 * hse2prs.cpp
 *
 *  Created on: Oct 29, 2020
 *      Author: nbingham
 */

#include "hse2prs.h"

prs::production_rule_set hse_to_prs(const hse::graph &g)
{
	prs::production_rule_set result;

	vector<int> vars;
	for (size_t i = 0; i < g.transitions.size(); i++)
	{
		if (g.transitions[i].behavior == hse::transition::active and not g.transitions[i].is_vacuous() and not g.transitions[i].is_infeasible())
		{
			prs::production_rule rule;
			rule.local_action = g.transitions[i].local_action;
			rule.remote_action = g.transitions[i].remote_action;
			rule.guard = strengthen(petri::iterator(hse::transition::type, i));
			result.rules.push_back(rule);
		}
	}

	return result;
}

// Work backwards from an implicant until we hit a state
// in which our production rule should not fire, but does
// given the current guard expression. From there we work
// forward until we find a transition that separates the
// conflicting state from the implicant state. We then use
// a greedy algorithm to pick the smallest combination of
// values from that transition that will separate the two.

// The use of greedy is only needed when we need to use a
// passive transition to separate the two because passive
// transitions can be a complex expression and not just one
// variable and one value.
boolean::cover strengthen(petri::iterator firing)
{
	boolean::cover result;

	

	return result;
}


/*

	vector<size_t> vl, vl2;
	petri_index tid;
	canonical t;
	vector<bool> covered;
	minterm reset;

	rules.resize(net.vars.globals.size());
	for (size_t i = 0; i < net.T.size(); i++)
	{
		vl = net.T[i].predicate.vars();
		for (size_t j = 0; net.T[i].active && j < vl.size(); j++)
		{
			if ((net.T[i].predicate & canonical(vl[j], 1)) == 0)
			{
				// Check to make sure this firing is not vacuous
				vector<petri_index> p = net.prev(petri_index(i, false));
				canonical predicate = 1;
				for (size_t k = 0; k < p.size(); k++)
					predicate &= net.at(p[k]).predicate;

				if ((predicate >> canonical(vl[j], 0)) != predicate)
					rules[vl[j]].implicants[0].push_back(petri_index(i, false));
			}
			else if ((net.T[i].predicate & canonical(vl[j], 0)) == 0)
			{
				// Check to make sure this firing is not vacuous
				vector<petri_index> p = net.prev(petri_index(i, false));
				canonical predicate = 1;
				for (size_t k = 0; k < p.size(); k++)
					predicate &= net.at(p[k]).predicate;

				if ((predicate >> canonical(vl[j], 1)) != predicate)
					rules[vl[j]].implicants[1].push_back(petri_index(i, false));
			}
		}
	}

	size_t r = net.vars.find("reset");
	if (r == net.vars.globals.size())
		net.vars.globals.push_back(variable("reset"));

	for (size_t j = 0; j < net.M0.size(); j++)
	{
		for (size_t k = 0; k < net.at(net.M0[j]).predicate.terms.size(); k++)
		{
			if (j == 0 && k == 0)
				reset = net.at(net.M0[j]).predicate.terms[k];
			else
				reset |= net.at(net.M0[j]).predicate.terms[k];
		}
	}

	log("", "calculating rules", __FILE__, __LINE__);
	for (size_t vi = 0; vi < net.vars.globals.size(); vi++)
		if (net.vars.globals[vi].written)
		{
			log("", net.vars.globals[vi].name, __FILE__, __LINE__);
			rules[vi].uid = vi;
			rules[vi].guards[1] = 0;
			rules[vi].guards[0] = 0;
			rules[vi].explicit_guards[1] = 0;
			rules[vi].explicit_guards[0] = 0;

			for (size_t i = 0; i < 2; i++)
			{
				for (size_t j = 0; j < rules[vi].implicants[i].size(); j++)
				{
					tid = rules[vi].implicants[i][j];
					vl = net.at(tid).predicate.vars();
					vector<petri_index> ia = net.prev(tid);
					t = 1;
					for (size_t k = 0; k < ia.size(); k++)
						t &= net.at(ia[k]).predicate;

					for (size_t k = 0; k < t.terms.size();)
					{
						if (t.terms[k].val(vi) == (uint32_t)i)
							t.terms.erase(t.terms.begin() + k);
						else
							k++;
					}

					t = t.hide(vl);
					rules[vi].explicit_guards[i] |= t;

					log("", "start " + net.at(tid).predicate.print(net.vars), __FILE__, __LINE__);
					rules[vi].strengthen(net, i);
				}
			}

			if (reset.val(vi) == 1)
			{
				rules[vi].guards[1] |= canonical(r, 1);
				rules[vi].guards[0] &= canonical(r, 0);
			}
			else
			{
				rules[vi].guards[0] |= canonical(r, 1);
				rules[vi].guards[1] &= canonical(r, 0);
			}
		}

	log("", "done", __FILE__, __LINE__);

	return result;
}

}


void merge_guards(canonical &guard0, canonical implicant0, canonical &guard1, canonical implicant1)
{
	// If the two guards are derived from the same minterm then ORing them together will create a conflict
	// so we need to merge them.
	if ((guard0 & implicant0) == (guard1 & implicant1))
	{
		guard0 &= guard1;
		guard1 = guard0;
	}
	else if (guard0 != guard1 && mergible(&guard0, &guard1))
	{
		canonical temp = guard0;
		canonical temp2 = guard1;

		if ((guard0 | guard1) == guard0)
		{
			canonical temp3 = 0;
			bool found = true;
			for (size_t l = 0; l < temp.terms.size() && found; l++)
			{
				vector<size_t> vlist = temp.terms[l].vars();
				found = false;
				for (size_t m = 1; m <= vlist.size() && !found; m++)
				{
					vector<size_t> comb = first_combination(m);
					do
					{
						canonical temp4;
						for (size_t n = 0; n < comb.size(); n++)
							temp4 = (n == 0 ? canonical(vlist[comb[n]], temp.terms[l].val(vlist[comb[n]]))  :
									  temp4 & canonical(vlist[comb[n]], temp.terms[l].val(vlist[comb[n]])) );

						if (!is_mutex(&temp4, &guard0, &implicant0) && is_mutex(&temp4, &temp2))
						{
							temp3 |= temp4;
							found = true;
						}
					} while (next_combination(vlist.size(), &comb) && !found);
					comb.clear();
				}
				vlist.clear();
			}

			if (!found)
				guard0 &= guard1;
			else
				guard0 &= temp3;
		}
		else if ((guard0 | guard1) == guard1)
		{
			canonical temp3 = 0;
			bool found = true;
			for (size_t l = 0; l < temp2.terms.size() && found; l++)
			{
				vector<size_t> vlist = temp2.terms[l].vars();
				found = false;
				for (size_t m = 1; m <= vlist.size() && !found; m++)
				{
					vector<size_t> comb = first_combination(m);
					do
					{
						canonical temp4;
						for (size_t n = 0; n < comb.size(); n++)
							temp4 = (n == 0 ? canonical(vlist[comb[n]], temp2.terms[l].val(vlist[comb[n]]))  :
									  temp4 & canonical(vlist[comb[n]], temp2.terms[l].val(vlist[comb[n]])) );

						if (!is_mutex(&temp4, &guard1, &implicant1) && is_mutex(&temp4, &temp))
						{
							temp3 |= temp4;
							found = true;
						}
					} while (next_combination(vlist.size(), &comb) && !found);
					comb.clear();
				}
				vlist.clear();
			}

			if (!found)
				guard1 &= guard0;
			else
				guard1 &= temp3;
		}
		else
		{
			canonical temp3 = 0;
			bool found = true;
			for (size_t l = 0; l < temp.terms.size() && found; l++)
			{
				vector<size_t> vlist = temp.terms[l].vars();
				found = false;
				for (size_t m = 1; m <= vlist.size() && !found; m++)
				{
					vector<size_t> comb = first_combination(m);
					do
					{
						canonical temp4;
						for (size_t n = 0; n < comb.size(); n++)
							temp4 = (n == 0 ? canonical(vlist[comb[n]], temp.terms[l].val(vlist[comb[n]]))  :
									  temp4 & canonical(vlist[comb[n]], temp.terms[l].val(vlist[comb[n]])) );

						if (!is_mutex(&temp4, &guard0, &implicant0) && is_mutex(&temp4, &temp2))
						{
							temp3 |= temp4;
							found = true;
						}
					} while (next_combination(vlist.size(), &comb) && !found);
					comb.clear();
				}
				vlist.clear();
			}

			if (!found)
				guard0 &= guard1;
			else
				guard0 &= temp3;

			temp3 = 0;
			found = true;
			for (size_t l = 0; l < temp2.terms.size() && found; l++)
			{
				vector<size_t> vlist = temp2.terms[l].vars();
				found = false;
				for (size_t m = 1; m <= vlist.size() && !found; m++)
				{
					vector<size_t> comb = first_combination(m);
					do
					{
						canonical temp4;
						for (size_t n = 0; n < comb.size(); n++)
							temp4 = (n == 0 ? canonical(vlist[comb[n]], temp2.terms[l].val(vlist[comb[n]]))  :
									  temp4 & canonical(vlist[comb[n]], temp2.terms[l].val(vlist[comb[n]])) );

						if (!is_mutex(&temp4, &guard1, &implicant1) && is_mutex(&temp4, &temp))
						{
							temp3 |= temp4;
							found = true;
						}
					} while (next_combination(vlist.size(), &comb) && !found);
					comb.clear();
				}
				vlist.clear();
			}

			if (!found)
				guard1 &= guard0;
			else
				guard1 &= temp3;
		}
	}
}

reduction_index::reduction_index()
{
	conflict = false;
	placeholder = false;
}

reduction_index::reduction_index(petri_index i, bool placeholder)
{
	this->data = i.data;
	this->conflict = false;
	this->placeholder = placeholder;
}

reduction_index::~reduction_index()
{

}

reduction_index &reduction_index::operator=(petri_index i)
{
	data = i.data;
	return *this;
}

ostream &operator<<(ostream &os, reduction_index r)
{
	os << *(petri_index*)&r << (r.conflict ? "!" : "") << (r.placeholder ? ":" : "");
	return os;
}

reductionhdl::reductionhdl()
{
	separator = 0;
}

reductionhdl::reductionhdl(const reductionhdl &r)
{
	implicant = r.implicant;
	guard = r.guard;
	covered = r.covered;
	begin = r.begin;
	end = r.end;
	separator = r.separator;
}

reductionhdl::reductionhdl(petri_net &net, petri_index start)
{
	if (start.is_trans())
		begin = net.prev(start);
	else
		begin = vector<petri_index>(1, start);

	implicant = 1;
	guard = 1;
	for (size_t j = 0; j < begin.size(); j++)
		implicant &= net.at(begin[j]).predicate;

	vector<petri_index> init = net.get_cut(begin, true, false);
	for (size_t k = 0; k < init.size(); k++)
		end.push_back(reduction_index(init[k], find(begin.begin(), begin.end(), init[k]) == begin.end()));

	covered.resize(net.S.size() + net.T.size(), false);
	separator = (int)net.S.size();
}

reductionhdl::~reductionhdl()
{

}

void reductionhdl::set_covered(petri_index i)
{
	int idx = i.idx();
	if (i.is_trans())
		idx += separator;

	covered[idx] = true;
}

bool reductionhdl::is_covered(petri_index i)
{
	int idx = i.idx();
	if (i.is_trans())
		idx += separator;

	return covered[idx];
}

reductionhdl &reductionhdl::operator=(reductionhdl r)
{
	implicant = r.implicant;
	guard = r.guard;
	covered = r.covered;
	begin = r.begin;
	end = r.end;
	separator = r.separator;
	return *this;
}

rule::rule()
{
	this->uid = -1;
	guards[0] = 0;
	guards[1] = 0;
	explicit_guards[0] = 0;
	explicit_guards[1] = 0;
	implicants[0] = vector<petri_index>();
	implicants[1] = vector<petri_index>();
}

rule::rule(int uid)
{
	this->uid = uid;
	guards[0] = 0;
	guards[1] = 0;
	explicit_guards[0] = 0;
	explicit_guards[1] = 0;
	implicants[0] = vector<petri_index>();
    implicants[1] = vector<petri_index>();
}

rule::rule(variable_space &vars, string u, string d, string v)
{
	implicants[0] = vector<petri_index>();
    implicants[1] = vector<petri_index>();

	uid = vars.find(v);

	guards[1] = canonical(u, vars);
	guards[0] = canonical(d, vars);
}

rule::~rule()
{
	this->uid = -1;
	guards[0] = 0;
	guards[1] = 0;
	explicit_guards[0] = 0;
	explicit_guards[1] = 0;
	implicants[0] = vector<petri_index>();
    implicants[1] = vector<petri_index>();
}

rule &rule::operator=(rule r)
{
	uid = r.uid;
	guards[1] = r.guards[1];
	guards[0] = r.guards[0];
	explicit_guards[0] = r.explicit_guards[0];
	explicit_guards[1] = r.explicit_guards[1];
	implicants[0] = r.implicants[0];
    implicants[1] = r.implicants[1];
	return *this;
}

bool rule::separate(petri_net &net, reductionhdl &reduction, int t)
{
	vector<petri_index> conflict;
	canonical encoding = 1;
	list<vector<petri_index> > executions(1, vector<petri_index>());
	for (size_t i = 0; i < reduction.end.size(); i++)
	{
		if (reduction.end[i].conflict && !reduction.end[i].placeholder)
		{
			conflict.push_back(reduction.end[i]);
			encoding &= net.at(reduction.end[i]).effective;
		}
		executions.back().push_back(reduction.end[i]);
	}

	log("", "conflict " + to_string(reduction.begin) + " <-- " + to_string(conflict) + "{" + encoding.print(net.vars) + "}", __FILE__, __LINE__);
	bool found = false;
	while (!found && executions.size() > 0)
	{
		for (list<vector<petri_index> >::iterator exec = executions.begin(); !found && exec != executions.end(); )
		{
			bool is_state = true;
			for (size_t j = 0; is_state && j < exec->size(); j++)
				if (exec->at(j).is_trans())
					is_state = false;

			if (is_state)
			{
				canonical transitions = 1;
				for (size_t j = 0; j < exec->size(); j++)
				{
					vector<petri_index> o = net.next(exec->at(j));
					vector<petri_index> valid_o;
					for (size_t l = 0; l < o.size(); l++)
						if (reduction.is_covered(o[l]))
						{
							valid_o.push_back(o[l]);
							log("", "\t\t" + to_string(o[l]), __FILE__, __LINE__);
						}

					if (valid_o.size() > 0)
					{
						canonical transition_term;
						for (size_t k = 0; k < valid_o.size(); k++)
							for (size_t l = 0; l < net.at(valid_o[k]).predicate.terms.size(); l++)
								if (net.at(valid_o[k]).predicate.terms[l].val(uid) != (uint32_t)t)
									transition_term |= canonical(net.at(valid_o[k]).predicate.terms[l]);
						transitions &= transition_term;
					}
				}

				log("", "\t\tT=" + transitions.print(net.vars), __FILE__, __LINE__);

				canonical temp2 = 0;
				found = (transitions != 0);
				for (size_t l = 0; l < transitions.terms.size() && found; l++)
				{
					vector<size_t> vlist = transitions.terms[l].vars();
					found = false;
					for (size_t j = 1; j <= vlist.size() && !found; j++)
					{
						vector<size_t> comb = first_combination(j);
						do
						{
							canonical temp = reduction.guard;
							canonical legal_check = 0;
							for (size_t k = 0; k < comb.size(); k++)
							{
								temp &= canonical(vlist[comb[k]], transitions.terms[l].val(vlist[comb[k]]));
								legal_check |= canonical(vlist[comb[k]], 1-transitions.terms[l].val(vlist[comb[k]]));
							}

							bool legal = false;
							for (size_t k = 0; !legal && k < reduction.implicant.terms.size(); k++)
								if ((reduction.guard & reduction.implicant.terms[k]) != 0 && (legal_check & reduction.guard & reduction.implicant.terms[k]) == 0)
									legal = true;

							log("", "testing " + temp.print(net.vars) + " " + (temp & encoding).print(net.vars), __FILE__, __LINE__);
							if (legal && temp != 0 && (canonical(uid, 1-t) & temp & encoding) == 0)
							{
								temp2 |= temp;
								log("", to_string(legal) + " " + temp.print(net.vars) + " " + temp2.print(net.vars) + " " + legal_check.print(net.vars), __FILE__, __LINE__);
								found = true;
							}
						} while (next_combination(vlist.size(), &comb) && !found);
						comb.clear();
					}
					vlist.clear();
				}

				if (found)
				{
					log("", "\tfound " + temp2.print(net.vars), __FILE__, __LINE__);
					reduction.guard = temp2;
				}
			}

			vector<pair<size_t, vector<petri_index> > > ready_places;
			vector<pair<size_t, vector<petri_index> > > ready_transitions;
			for (size_t i = 0; !found && i < exec->size(); i++)
			{
				vector<petri_index> n = net.next(exec->at(i));
				if (find(reduction.begin.begin(), reduction.begin.end(), exec->at(i)) == reduction.begin.end())
				{
					if (exec->at(i).is_place())
					{
						size_t total = 0;
						for (size_t k = i; k < exec->size(); k++)
							if (net.next(exec->at(k))[0] == n[0])
								total++;

						vector<petri_index> p = net.prev(n);
						p.resize(unique(p.begin(), p.end()) - p.begin());
						if (total == p.size())
						{
							ready_places.push_back(pair<int, vector<petri_index> >(i, vector<petri_index>()));

							for (size_t j = 0; j < n.size(); j++)
								if (reduction.is_covered(n[j]))
									ready_places.back().second.push_back(n[j]);

							if (ready_places.back().second.size() == 0)
								ready_places.pop_back();
						}
					}
					else
					{
						ready_transitions.push_back(pair<int, vector<petri_index> >(i, vector<petri_index>()));

						for (size_t j = 0; j < n.size(); j++)
							if (reduction.is_covered(n[j]))
								ready_transitions.back().second.push_back(n[j]);

						if (ready_transitions.back().second.size() == 0)
							ready_transitions.pop_back();
					}
				}
			}

			//log("", to_string(exec->state) + " " + exec->trans.print(vars), __FILE__, __LINE__);

			if (!found && ready_transitions.size() > 0)
			{
				log("", "\t" + to_string(*exec), __FILE__, __LINE__);
				for (size_t i = ready_transitions.size()-1; i >= 0 && i < ready_transitions.size(); i--)
				{
					for (size_t j = ready_transitions[i].second.size()-1; j >= 0 && j < ready_transitions[i].second.size(); j--)
					{
						if (j > 0)
							exec->push_back(ready_transitions[i].second[j]);
						else
							exec->at(ready_transitions[i].first) = ready_transitions[i].second[j];
					}
				}
				exec++;
			}
			else if (!found && ready_places.size() > 0)
			{
				log("", "\t" + to_string(*exec), __FILE__, __LINE__);
				for (size_t i = ready_places.size()-1; i >= 0 && i < ready_places.size(); i--)
				{
					list<vector<petri_index> >::iterator curr = exec;
					if (i > 0)
					{
						executions.push_back(*exec);
						curr = executions.end();
						--curr;
					}

					for (size_t k = ready_places[i].first+1; k < exec->size(); )
					{
						if (net.next(exec->at(k))[0] == net.next(exec->at(ready_places[i].first))[0])
						{
							for (size_t j = i+1; j < ready_places.size(); j++)
								if (ready_places[j].first > k)
									ready_places[j].first--;

							exec->erase(exec->begin() + k);
						}
						else
							k++;
					}

					for (size_t j = ready_places[i].second.size()-1; j >= 0 && j < ready_places[i].second.size(); j--)
					{
						if (j > 0)
						{
							executions.push_back(*curr);
							executions.back().at(ready_places[i].first) = ready_places[i].second[j];
						}
						else
							curr->at(ready_places[i].first) = ready_places[i].second[j];
					}
				}
				exec++;
			}
			else
			{
				exec = executions.erase(exec);
				log("", "\texecution done", __FILE__, __LINE__);
			}
		}
	}

	if (!found)
	{
		cout << reduction.end << endl;
		error(net.name, to_string(conflict) + " conflicts with implicant " + to_string(reduction.begin), "", __FILE__, __LINE__);
		return false;
	}

	return true;
}

void rule::strengthen(petri_net &net, int t)
{
	list<reductionhdl> reductions;
	for (size_t i = 0; i < implicants[t].size(); i++)
		reductions.push_back(reductionhdl(net, implicants[t][i]));

	for (list<reductionhdl>::iterator reduction = reductions.begin(); reduction != reductions.end(); reduction++)
	{
		log("", "begin execution", __FILE__, __LINE__);
		// Work backwards from an implicant until we hit a state
		// in which our production rule should not fire, but does
		// given the current guard expression. From there we work
		// forward until we find a transition that separates the
		// conflicting state from the implicant state. We then use
		// the greedy algorithm to pick the smallest combination of
		// values from that transition that will separate the two.

		// The use of greedy is only needed when we need to use a
		// passive transition to separate the two because passive
		// transitions can be a complex expression and not just one
		// variable and one value.
		bool done = false;
		bool stuck = false;
		while (!done)
		{
			log("", to_string(reduction->end) + " " + reduction->guard.print(net.vars), __FILE__, __LINE__);

			bool conflict = true;
			for (size_t i = 0; i < reduction->end.size(); i++)
				if (!reduction->end[i].conflict && !reduction->end[i].placeholder)
					conflict = false;

			if (stuck)
				conflict = true;

			bool success = true;
			if (conflict)
			{
				success = separate(net, *reduction, t);
				stuck = false;
			}

			// This is the meat of the whole function. At this point,
			// we have reached a new state (where all indices are at
			// a place) and we need to determine whether or not we
			// need to add a transition to separate this place from
			// our initial implicant.
			for (size_t i = 0; i < reduction->end.size(); i++)
			{
				if (!reduction->end[i].placeholder)
				{
					if (conflict && !success)
						reduction->end[i].conflict = false;
					else if (((conflict && success) || !reduction->end[i].conflict) && reduction->end[i].is_place())
					{
						// Check to see if we need to separate this state from the
						// implicant by looking for a transition to add in.
						vector<petri_index> o = net.next(reduction->end[i]);
						o.resize(unique(o.begin(), o.end()) - o.begin());
						bool is_implicant = false;
						for (size_t j = 0; !is_implicant && j < implicants[t].size(); j++)
						{
							if (net.are_parallel_siblings(implicants[t][j], reduction->end[i]))
								is_implicant = true;

							for (size_t k = 0; !is_implicant && k < o.size(); k++)
								if (o[k] == implicants[t][j])
									is_implicant = true;
						}

						canonical encoding = net.at(reduction->end[i]).effective;

						log("", "checking " + to_string(reduction->end[i]) + " " + to_string(conflict) + " " + to_string(success) + " " + to_string(is_implicant) + " " + to_string(reduction->end[i].conflict) + " " + encoding.print(net.vars) + " " + (canonical(uid, 1-t) & reduction->guard & encoding).print(net.vars), __FILE__, __LINE__);

						// If this state needs to be separated from the implicant state,
						// work backwards in the path until we find the closest set of
						// transitions that separate them. Then, use greedy to get the
						// least number of values needed to separate them.
						if (!is_implicant && (canonical(uid, 1-t) & reduction->guard & encoding) != 0)
							reduction->end[i].conflict = true;
						else
							reduction->end[i].conflict = false;
					}
				}
			}

			// Figure out which indices are ready to be moved
			// and separate them out into places and transitions.
			vector<pair<size_t, vector<petri_index> > > ready_transitions;
			vector<pair<petri_index, vector<size_t> > > ready_places;
			for (size_t i = 0; i < reduction->end.size(); i++)
			{
				if (reduction->end[i].is_trans())
				{
					vector<petri_index> temp = net.prev(reduction->end[i]);
					vector<petri_index> n;
					for (size_t j = 0; j < temp.size(); j++)
						if (!reduction->is_covered(temp[j]))
							n.push_back(temp[j]);

					if (n.size() > 0)
						ready_transitions.push_back(pair<size_t, vector<petri_index> >(i, n));
				}
			}

			if (ready_transitions.size() == 0)
			{
				vector<petri_index> n;
				for (size_t i = 0; i < reduction->end.size(); i++)
				{
					if (!reduction->end[i].conflict && !reduction->end[i].placeholder)
					{
						vector<petri_index> temp = net.prev(reduction->end[i]);
						for (size_t j = 0; j < temp.size(); j++)
							if (!reduction->is_covered(temp[j]))
								n.push_back(temp[j]);
					}
				}
				sort(n.begin(), n.end());
				n.resize(unique(n.begin(), n.end()) - n.begin());
				sort(reduction->end.rbegin(), reduction->end.rend());

				for (size_t i = 0; i < n.size(); i++)
				{
					vector<petri_index> p = net.next(n[i]);

					vector<size_t> count;
					for (size_t j = 0, k = 0; j < reduction->end.size() && k < p.size(); )
					{
						if (reduction->end[j] > p[k])
							j++;
						else if (p[k] > reduction->end[j])
							k++;
						else
						{
							if (!reduction->end[j].conflict)
								count.push_back(j);
							j++;
							k++;
						}
					}

					if (count.size() == p.size())
						ready_places.push_back(pair<petri_index, vector<size_t> >(n[i], count));
				}
			}

			// Transitions are always handled first to ensure that
			// we will reach a valid state.
			if (ready_transitions.size() > 0)
			{
				for (size_t i = 0; i < ready_transitions.size(); i++)
				{
					if (!reduction->end[ready_transitions[i].first].placeholder)
						reduction->set_covered(reduction->end[ready_transitions[i].first]);

					for (size_t j = 0; j < ready_transitions[i].second.size(); j++)
					{
						if (j < ready_transitions[i].second.size()-1)
						{
							reduction->end.push_back(reduction->end[ready_transitions[i].first]);
							reduction->end.back() = ready_transitions[i].second[j];
						}
						else
							reduction->end[ready_transitions[i].first] = ready_transitions[i].second[j];
					}
				}
			}
			// Then places are handled. Every ordering of moving
			// from a place to a transition creates a new possible
			// execution.
			else if (ready_places.size() > 0)
			{
				// Group them so that we can handle as many as we can without duplicating executions
				// This is strictly a runtime optimization
				vector<vector<size_t> > groupings;
				for (size_t i = 0; i < ready_places.size(); i++)
				{
					vector<size_t> found;
					for (size_t j = 0; j < groupings.size(); j++)
						for (size_t k = 0; k < groupings[j].size(); k++)
							if (vector_intersection_size(&ready_places[groupings[j][k]].second, &ready_places[i].second) > 0)
								found.push_back(j);

					sort(found.rbegin(), found.rend());
					found.resize(unique(found.begin(), found.end()) - found.begin());
					if (found.size() == 0)
						groupings.push_back(vector<size_t>(1, i));
					else
					{
						for (size_t j = 0; j < found.size()-1; j++)
						{
							groupings[found[found.size()-1]].insert(groupings[found[found.size()-1]].end(), groupings[found[j]].begin(), groupings[found[j]].end());
							groupings.erase(groupings.begin() + found[j]);
						}

						groupings[found[found.size()-1]].push_back(i);

						sort(groupings[found[found.size()-1]].begin(), groupings[found[found.size()-1]].end());
						groupings[found[found.size()-1]].resize(unique(groupings[found[found.size()-1]].begin(), groupings[found[found.size()-1]].end()) - groupings[found[found.size()-1]].begin());
					}
				}

				vector<vector<size_t> > valid_paths;
				vector<size_t> iter(groupings.size(), 0);
				bool last = false;
				while (!last)
				{
					last = true;
					for (size_t i = 0; last && i < iter.size(); i++)
						if (iter[i] < groupings[i].size()-1)
							last = false;

					valid_paths.push_back(iter);

					iter[0]++;
					for (size_t i = 0; i < iter.size()-1 && iter[i] >= groupings[i].size(); i++)
					{
						iter[i] = 0;
						iter[i+1]++;
					}
				}

				// remove invalid paths... i.e. paths for which we have
				// a pair of ends that are not in parallel.
				for (size_t i = 0; i < valid_paths.size(); )
				{
					bool valid = true;
					vector<petri_index> n;
					vector<size_t> used;
					for (size_t j = 0; j < groupings.size(); j++)
					{
						n.push_back(ready_places[groupings[j][valid_paths[i][j]]].first);
						used.insert(used.end(), ready_places[groupings[j][valid_paths[i][j]]].second.begin(), ready_places[groupings[j][valid_paths[i][j]]].second.end());
					}

					sort(used.begin(), used.end());
					used.resize(unique(used.begin(), used.end()) - used.begin());

					for (size_t j = 0; j < reduction->end.size(); j++)
						if (find(used.begin(), used.end(), j) == used.end())
							n.push_back(reduction->end[j]);

					sort(n.begin(), n.end());
					n.resize(unique(n.begin(), n.end()) - n.begin());
					for (size_t j = 0; valid && j < n.size(); j++)
						for (size_t k = j+1; valid && k < n.size(); k++)
							if (!net.are_parallel_siblings(n[j], n[k]))
								valid = false;

					if (!valid)
						valid_paths.erase(valid_paths.begin() + i);
					else
						i++;
				}

				for (size_t i = 0; i < valid_paths.size(); i++)
				{
					// ****************************** This is the important stuff *****************************
					list<reductionhdl>::iterator temp_reduction = reduction;
					if (i < valid_paths.size()-1)
					{
						reductions.push_back(*reduction);
						temp_reduction = reductions.end();
						temp_reduction--;
					}

					vector<size_t> remove;
					for (size_t j = 0; j < groupings.size(); j++)
					{
						if (!temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[0]].placeholder)
							temp_reduction->set_covered(temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[0]]);
						temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[0]].placeholder = false;
						temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[0]] = ready_places[groupings[j][valid_paths[i][j]]].first;

						for (size_t k = ready_places[groupings[j][valid_paths[i][j]]].second.size()-1; k > 0; k--)
						{
							if (!temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[k]].placeholder)
								temp_reduction->set_covered(temp_reduction->end[ready_places[groupings[j][valid_paths[i][j]]].second[k]]);
							remove.push_back(ready_places[groupings[j][valid_paths[i][j]]].second[k]);
						}
					}

					sort(remove.rbegin(), remove.rend());
					remove.resize(unique(remove.begin(), remove.end()) - remove.begin());

					for (size_t k = 0; k < remove.size(); k++)
						temp_reduction->end.erase(temp_reduction->end.begin() + remove[k]);

					// ****************************************************************************************
				}
			}
			else
			{
				for (size_t i = 0; !stuck && i < reduction->end.size(); i++)
					if (reduction->end[i].conflict)
						stuck = true;

				if (!stuck)
					done = true;
			}
		}
	}

	// Once we are done with the above, there is still one more step.
	// If you have two rules {x->z-, x&y->z-} and you OR them together,
	// then you would end up with {x->z-}. This would create a conflict,
	// causing the {x&y->z-} rule to fire where it shouldn't. If we AND
	// them together, we would get {x&y->z-}. This would prevent the
	// {x->z-} rule from firing when it needs to.
	
	// So instead of doing either of these operations, we need to pick
	// some values that we can AND into each or either rule to separate
	// them. For example {x->z-, x&y->z-} would turn into {x&w->z-, x&y->z-}
	// making them now safe to OR, resulting in the rule {x&w|x&y->z-}.
	
	// This does not need to be done if the two rules are exactly equal,
	// only if information is lost by ORing the two together. To check this,
	// you need to go back to The Quine McCluskey algorithm to see when it
	// decides to merge minterms.
	
	// Picking the right information is just a matter of the greedy algorithm.
	// Look for the smallest combination of values that separates the two
	// minterms and use that.
	vector<pair<canonical, canonical> > temp_guards;
	log("", "result", __FILE__, __LINE__);
	for (list<reductionhdl>::iterator reduction = reductions.begin(); reduction != reductions.end(); reduction++)
	{
		if (reduction->guard != 1)
		{
			bool found = false;
			for (size_t i = 0; !found && i < temp_guards.size(); i++)
				if (temp_guards[i].first == reduction->guard)
				{
					temp_guards[i].second &= reduction->implicant;
					found = true;
				}

			if (!found)
			{
				temp_guards.push_back(pair<canonical, canonical>(reduction->guard, reduction->implicant));
				log("", reduction->guard.print(net.vars) + " -> " + net.vars.globals[uid].name + (t == 1 ? "+" : "-"), __FILE__, __LINE__);
			}
		}
	}
	reductions.clear();

	for (size_t j = 0; j < temp_guards.size(); j++)
		for (size_t k = j+1; k < temp_guards.size(); k++)
			merge_guards(temp_guards[j].first, temp_guards[j].second, temp_guards[k].first, temp_guards[k].second);

	for (size_t j = 0; j < temp_guards.size(); j++)
		guards[t] |= temp_guards[j].first;
}

canonical &rule::up()
{
	return guards[1];
}

canonical &rule::down()
{
	return guards[0];
}

// This check assumes that this rule is valid
bool rule::is_combinational()
{
	return ((guards[0] | guards[1]) == 1);
}

void rule::invert()
{
	canonical temp = guards[0];
	guards[0] = guards[1];
	guards[1] = temp;
	temp = explicit_guards[0];
	explicit_guards[0] = explicit_guards[1];
	explicit_guards[1] = temp;
	vector<petri_index> tempimp = implicants[0];
	implicants[0] = implicants[1];
	implicants[1] = tempimp;
}

//Print the rule in the following format:
//guards[1] left -> guards[1] right+
//guards[0] left -> guards[0] right-
void rule::print(variable_space &vars, ostream &os, string prefix)
{
	if (guards[1] != -1)
		os << guards[1].print_with_quotes(vars, prefix) << " -> \"" << prefix << vars.globals[uid].name << "\"+" << endl;
	if (guards[0] != -1)
		os << guards[0].print_with_quotes(vars, prefix) << " -> \"" << prefix << vars.globals[uid].name << "\"-" << endl;
}

*/



/*void rule_space::generate_minterms(petri_net &net)
{
	vector<size_t> vl, vl2;
	petri_index tid;
	canonical t;
	vector<bool> covered;
	minterm reset;

	rules.resize(net.vars.globals.size());
	for (size_t i = 0; i < net.T.size(); i++)
	{
		vl = net.T[i].predicate.vars();
		for (size_t j = 0; net.T[i].active && j < vl.size(); j++)
		{
			if ((net.T[i].predicate & canonical(vl[j], 1)) == 0)
			{
				// Check to make sure this firing is not vacuous
				vector<petri_index> p = net.prev(petri_index(i, false));
				canonical predicate = 1;
				for (size_t k = 0; k < p.size(); k++)
					predicate &= net.at(p[k]).predicate;

				if ((predicate >> canonical(vl[j], 0)) != predicate)
					rules[vl[j]].implicants[0].push_back(petri_index(i, false));
			}
			else if ((net.T[i].predicate & canonical(vl[j], 0)) == 0)
			{
				// Check to make sure this firing is not vacuous
				vector<petri_index> p = net.prev(petri_index(i, false));
				canonical predicate = 1;
				for (size_t k = 0; k < p.size(); k++)
					predicate &= net.at(p[k]).predicate;

				if ((predicate >> canonical(vl[j], 1)) != predicate)
					rules[vl[j]].implicants[1].push_back(petri_index(i, false));
			}
		}
	}

	size_t r = net.vars.find("reset");
	if (r == net.vars.globals.size())
		net.vars.globals.push_back(variable("reset"));

	for (size_t j = 0; j < net.M0.size(); j++)
	{
		for (size_t k = 0; k < net.at(net.M0[j]).predicate.terms.size(); k++)
		{
			if (j == 0 && k == 0)
				reset = net.at(net.M0[j]).predicate.terms[k];
			else
				reset |= net.at(net.M0[j]).predicate.terms[k];
		}
	}

	log("", "calculating rules", __FILE__, __LINE__);
	for (size_t vi = 0; vi < net.vars.globals.size(); vi++)
		if (net.vars.globals[vi].written)
		{
			log("", net.vars.globals[vi].name, __FILE__, __LINE__);
			rules[vi].uid = vi;
			rules[vi].guards[1] = 0;
			rules[vi].guards[0] = 0;
			rules[vi].explicit_guards[1] = 0;
			rules[vi].explicit_guards[0] = 0;

			for (size_t i = 0; i < 2; i++)
			{
				for (size_t j = 0; j < rules[vi].implicants[i].size(); j++)
				{
					tid = rules[vi].implicants[i][j];
					vl = net.at(tid).predicate.vars();
					vector<petri_index> ia = net.prev(tid);
					t = 1;
					for (size_t k = 0; k < ia.size(); k++)
						t &= net.at(ia[k]).predicate;

					for (size_t k = 0; k < t.terms.size();)
					{
						if (t.terms[k].val(vi) == (uint32_t)i)
							t.terms.erase(t.terms.begin() + k);
						else
							k++;
					}

					t = t.hide(vl);
					rules[vi].explicit_guards[i] |= t;

					log("", "start " + net.at(tid).predicate.print(net.vars), __FILE__, __LINE__);
					rules[vi].strengthen(net, i);
				}
			}

			if (reset.val(vi) == 1)
			{
				rules[vi].guards[1] |= canonical(r, 1);
				rules[vi].guards[0] &= canonical(r, 0);
			}
			else
			{
				rules[vi].guards[0] |= canonical(r, 1);
				rules[vi].guards[1] &= canonical(r, 0);
			}
		}

	log("", "done", __FILE__, __LINE__);
}

void rule_space::check(petri_net &net)
{
	bool has_error = false;
	for (size_t i = 0; i < net.S.size(); i++)
	{
		vector<petri_index> oa = net.next(petri_index(i, true));
		for (size_t j = 0; j < rules.size(); j++)
			for (size_t k = 0; k < 2; k++)
				if (rules[j].implicants[k].size() > 0)
				{
					bool para = false;
					for (size_t l = 0; l < rules[j].implicants[k].size() && !para; l++)
						if (net.are_parallel_siblings(petri_index(i, true), rules[j].implicants[k][l]))
							para = true;

					bool imp = false;
					for (size_t l = 0; l < oa.size() && !imp; l++)
						if (find(rules[j].implicants[k].begin(), rules[j].implicants[k].end(), oa[l]) != rules[j].implicants[k].end())
							imp = true;

					// Does it fire when it shouldn't?
					if (!imp && !para)
					{
						canonical shouldnt = rules[j].guards[k] & net.S[i].effective & canonical(rules[j].uid, 1-k) & canonical(net.vars.find("reset"), 0);
						if (shouldnt != 0)
						{
							has_error = true;
							error(net.name, net.vars.globals[rules[j].uid].name + (k == 0 ? "-" : "+") + " fires when it shouldn't at " + to_string(petri_index(i, true)), "", __FILE__, __LINE__);
						}
					}
					// Does it fire when it should?
					else if (imp)
					{
						canonical should = (~rules[j].guards[k]) & net.S[i].predicate & canonical(net.vars.find("reset"), 0) & canonical(rules[j].uid, 1-k);

						if (should != 0)
						{
							vector<size_t> names;
							for (size_t l = 0; l < rules[j].guards[k].terms.size(); l++)
								for (size_t m = 0; m < net.S[i].predicate.terms.size(); m++)
								{
									minterm test = rules[j].guards[k].terms[l] & net.S[i].predicate.terms[m];

									for (size_t n = 0; n < net.vars.globals.size(); n++)
										if (test.val(n) == (uint32_t)-1)
											names.push_back(n);
								}

							sort(names.begin(), names.end());
							names.resize(unique(names.begin(), names.end()) - names.begin());

							string tempstr;
							for (size_t l = 0; l < names.size(); l++)
							{
								if (l != 0 && names.size() > 2)
									tempstr += ", ";
								else if (l != 0)
									tempstr += " ";

								if (l == names.size()-1 && names.size() > 1)
									tempstr += "and ";

								tempstr += net.vars.globals[names[l]].name;
							}

							has_error = true;
							error(net.name, net.vars.globals[rules[j].uid].name + (k == 0 ? "-" : "+") + " doesn't fire when it should at " + (para ? "parallel " : "") + (imp ? "implicant " : "") + "place " + to_string(petri_index(i, true)), "The values of " + tempstr + " in the guard conflict with the predicate for " + to_string(petri_index(i, true)), __FILE__, __LINE__);
						}
					}
					else if (para)
					{
						canonical should = rules[j].guards[k] & net.S[i].predicate & canonical(net.vars.find("reset"), 0);

						if (should == 0)
						{
							vector<size_t> names;
							for (size_t l = 0; l < rules[j].guards[k].terms.size(); l++)
								for (size_t m = 0; m < net.S[i].predicate.terms.size(); m++)
								{
									minterm test = rules[j].guards[k].terms[l] & net.S[i].predicate.terms[m];

									for (size_t n = 0; n < net.vars.globals.size(); n++)
										if (test.val(n) == (uint32_t)-1)
											names.push_back(n);
								}

							sort(names.begin(), names.end());
							names.resize(unique(names.begin(), names.end()) - names.begin());

							string tempstr;
							for (size_t l = 0; l < names.size(); l++)
							{
								if (l != 0 && names.size() > 2)
									tempstr += ", ";
								else if (l != 0)
									tempstr += " ";

								if (l == names.size()-1 && names.size() > 1)
									tempstr += "and ";

								tempstr += net.vars.globals[names[l]].name;
							}

							has_error = true;
							error(net.name, net.vars.globals[rules[j].uid].name + (k == 0 ? "-" : "+") + " doesn't fire when it should at " + (para ? "parallel " : "") + (imp ? "implicant " : "") + "place " + to_string(petri_index(i, true)), "The values of " + tempstr + " in the guard conflict with the predicate for " + to_string(petri_index(i, true)), __FILE__, __LINE__);
						}
					}
				}
	}

	if (has_error)
		net.export_dot(0, 0).print();
}

void rule_space::generate_bubble(variable_space &vars)
{
	vector<pair<int, int> > bnet;

	vector<size_t> tvars, ivars;

	for (size_t i = 0; i < rules.size(); i++)
		for (int j = 0; j < 2; j++)
			for (size_t k = 0; k < rules[i].guards[j].terms.size(); k++)
			{
				ivars = rules[i].guards[j].terms[k].vars();
				for (size_t l = 0; l < ivars.size(); l++)
					bnet.push_back(pair<int, int>(ivars[l]*2 + rules[i].guards[j].terms[k].val(ivars[l]), rules[i].uid*2 + j));
			}

	bnet.resize(unique(bnet.begin(), bnet.end()) - bnet.begin());

	vector<pair<int, int> >::iterator remarc;
	for (size_t i = 0; i < vars.globals.size(); i++)
		for (size_t j = 0; j < vars.globals.size(); j++)
			if (i != j)
			{
				if ((remarc = find(bnet.begin(), bnet.end(), pair<int, int>(i*2, j*2))) != bnet.end() && find(bnet.begin(), bnet.end(), pair<int, int>(i*2+1, j*2)) != bnet.end())
				{
					error("", "dividing signal found in production rules {" + vars.globals[i].name + " -> " + vars.globals[j].name + "-}", "", __FILE__, __LINE__);
					for (size_t k = 0; k < rules[remarc->second/2].guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);

					for (size_t k = 0; k < rules[remarc->second/2].explicit_guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].explicit_guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);
					bnet.erase(remarc);
				}

				if (find(bnet.begin(), bnet.end(), pair<int, int>(i*2, j*2+1)) != bnet.end() && (remarc = find(bnet.begin(), bnet.end(), pair<int, int>(i*2+1, j*2+1))) != bnet.end())
				{
					error("", "dividing signal found in production rules {" + vars.globals[i].name + " -> " + vars.globals[j].name + "+}", "", __FILE__, __LINE__);
					for (size_t k = 0; k < rules[remarc->second/2].guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);

					for (size_t k = 0; k < rules[remarc->second/2].explicit_guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].explicit_guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);
					bnet.erase(remarc);
				}

				if ((remarc = find(bnet.begin(), bnet.end(), pair<int, int>(i*2, j*2))) != bnet.end() && find(bnet.begin(), bnet.end(), pair<int, int>(i*2, j*2+1)) != bnet.end())
				{
					error("", "gating signal found in production rules {" + vars.globals[i].name + "- -> " + vars.globals[j].name + "}", "", __FILE__, __LINE__);
					for (size_t k = 0; k < rules[remarc->second/2].guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);

					for (size_t k = 0; k < rules[remarc->second/2].explicit_guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].explicit_guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);
					bnet.erase(remarc);
				}

				if (find(bnet.begin(), bnet.end(), pair<int, int>(i*2+1, j*2)) != bnet.end() && (remarc = find(bnet.begin(), bnet.end(), pair<int, int>(i*2+1, j*2+1))) != bnet.end())
				{
					error("", "gating signal found in production rules {" + vars.globals[i].name + "+ -> " + vars.globals[j].name + "}", "", __FILE__, __LINE__);
					for (size_t k = 0; k < rules[remarc->second/2].guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);

					for (size_t k = 0; k < rules[remarc->second/2].explicit_guards[remarc->second%2].terms.size(); k++)
						rules[remarc->second/2].explicit_guards[remarc->second%2].terms[k].sv_union(remarc->first/2, remarc->first%2 == 0 ? v1 : v0);
					bnet.erase(remarc);
				}
			}

	bubble_net.clear();
	map<pair<int, int>, pair<bool, bool> >::iterator net2iter;
	for (size_t i = 0; i < bnet.size(); i++)
	{
		net2iter = bubble_net.find(pair<int, int>(bnet[i].first/2, bnet[i].second/2));
		if (net2iter == bubble_net.end())
			bubble_net.insert(pair<pair<int, int>, pair<bool, bool> >(pair<int, int>(bnet[i].first/2, bnet[i].second/2), pair<bool, bool>(true, bnet[i].first%2 == bnet[i].second%2)));
		else
			net2iter->second.first = false;
	}
}

void rule_space::bubble_reshuffle(variable_space &vars, string name)
{
	cout << "Bubble Reshuffling " << name << endl;
	// Generate bubble reshuffle graph
	vector<bool> inverted(vars.globals.size(), false);
	vector<pair<vector<int>, bool> > cycles;

	// Execute bubble reshuffling algorithm
	for (map<pair<int, int>, pair<bool, bool> >::iterator i = bubble_net.begin(); i != bubble_net.end(); i++)
	{
		vector<pair<vector<int>, bool> > temp = reshuffle_algorithm(i, true, &bubble_net, vector<int>(), &inverted);
		cycles.insert(cycles.end(), temp.begin(), temp.end());
	}

	sort(cycles.begin(), cycles.end());
	cycles.resize(unique(cycles.begin(), cycles.end()) - cycles.begin());

	for (size_t i = 1; i < cycles.size(); i++)
		if (cycles[i].first == cycles[i-1].first)
		{
			cycles.erase(cycles.begin() + i);
			cycles.erase(cycles.begin() + i-1);
			i--;
		}

	for (size_t i = 0; i < cycles.size(); i++)
		if (cycles[i].second)
		{
			cycles.erase(cycles.begin() + i);
			i--;
		}

	// Remove Negative Cycles (currently negative cycles just throw an error message)
	for (size_t i = 0; i < cycles.size(); i++)
	{
		string tempstr;
		for (size_t j = 0; j < cycles[i].first.size(); j++)
		{
			if (j != 0)
				tempstr += ", ";
			tempstr += vars.globals[cycles[i].first[j]].name;
		}
		error("", "negative cycle found in process " + name, tempstr, __FILE__, __LINE__);
	}

	vector<variable> toadd;
	canonical temp;

	for (size_t i = 0; i < vars.globals.size(); i++)
		if (inverted[i])
		{
			for (size_t j = 0; j < rules.size(); j++)
				for (size_t k = 0; k < 2; k++)
					for (size_t l = 0; l < rules[j].guards[k].terms.size(); l++)
						rules[j].guards[k].terms[l].sv_not(i);

			rules[i].invert();

			toadd.push_back(vars.globals[i]);
			toadd.back().name = toadd.back().inverse_name();
		}

	for (size_t i = 0; i < toadd.size(); i++)
	{
		vars.globals.push_back(toadd[i]);

		if (toadd[i].written)
			rules.push_back(rule(vars, "~" + toadd[i].name, toadd[i].name, toadd[i].inverse_name()));
		else
			rules.push_back(rule(vars, "~" + toadd[i].inverse_name(), toadd[i].inverse_name(), toadd[i].name));
	}

	// Apply local inversions to production rules
	for (map<pair<int, int>, pair<bool, bool> >::iterator i = bubble_net.begin(); i != bubble_net.end(); i++)
	{
		if (i->second.second)
		{
			size_t vj = vars.find(vars.globals[i->first.first].inverse_name());
			if (vj == vars.globals.size())
			{
				vars.globals.push_back(vars.globals[i->first.first]);
				vars.globals.back().name = vars.globals[i->first.first].inverse_name();
				vj = vars.globals.size()-1;
				rules.push_back(rule(vars, "~" + vars.globals[i->first.first].name, vars.globals[i->first.first].name, vars.globals[i->first.first].inverse_name()));
			}

			for (size_t j = 0; j < 2; j++)
				for (size_t k = 0; k < rules[i->first.second].guards[j].terms.size(); k++)
				{
					rules[i->first.second].guards[j].terms[k].set(vj, rules[i->first.second].guards[j].terms[k].get(i->first.first));
					rules[i->first.second].guards[j].terms[k].sv_not(vj);
					rules[i->first.second].guards[j].terms[k].set(i->first.first, vX);
				}
		}
	}
}

vector<pair<vector<int>, bool> > rule_space::reshuffle_algorithm(map<pair<int, int>, pair<bool, bool> >::iterator idx, bool forward, map<pair<int, int>, pair<bool, bool> > *net, vector<int> cycle, vector<bool> *inverted)
{
	vector<pair<vector<int>, bool> > cycles;
	vector<int> negative_cycle;
	vector<int>::iterator found;

	cycle.push_back(forward ? idx->first.first : idx->first.second);

	found = find(cycle.begin(), cycle.end(), forward ? idx->first.second : idx->first.first);
	if (found == cycle.end())
	{
		if (idx->second.first && idx->second.second && forward)
		{
			(*inverted)[idx->first.second] = !(*inverted)[idx->first.second];
			for (map<pair<int, int>, pair<bool, bool> >::iterator j = net->begin(); j != net->end(); j++)
				if (j->first.first == idx->first.second || j->first.second == idx->first.second)
					j->second.second = !j->second.second;
		}
		else if (idx->second.first && idx->second.second && !forward)
		{
			(*inverted)[idx->first.first] = !(*inverted)[idx->first.first];
			for (map<pair<int, int>, pair<bool, bool> >::iterator j = net->begin(); j != net->end(); j++)
				if (j->first.first == idx->first.first || j->first.second == idx->first.first)
					j->second.second = !j->second.second;
		}

		for (map<pair<int, int>, pair<bool, bool> >::iterator i = net->begin(); cycles.size() == 0 && i != net->end(); i++)
		{
			vector<pair<vector<int>, bool> > temp;
			if (forward && (i->first.first == idx->first.second || i->first.second == idx->first.second) && i != idx)
				temp = reshuffle_algorithm(i, (i->first.first == idx->first.second), net, cycle, inverted);
			else if (!forward && (i->first.first == idx->first.first || i->first.second == idx->first.first) && i != idx)
				temp = reshuffle_algorithm(i, (i->first.first == idx->first.first), net, cycle, inverted);
			cycles.insert(cycles.end(), temp.begin(), temp.end());
		}
	}
	else
	{
		vector<int> temp(found, cycle.end());
		sort(temp.begin(), temp.end());
		temp.resize(unique(temp.begin(), temp.end()) - temp.begin());
		cycles.push_back(pair<vector<int>, bool>(temp, !idx->second.first || !idx->second.second));
	}

	sort(cycles.begin(), cycles.end());
	cycles.resize(unique(cycles.begin(), cycles.end()) - cycles.begin());

	for (size_t i = 1; i < cycles.size(); i++)
		if (cycles[i].first == cycles[i-1].first)
		{
			cycles.erase(cycles.begin() + i);
			cycles.erase(cycles.begin() + i-1);
			i--;
		}

	return cycles;
}

dot_graph rule_space::export_bubble(variable_space &vars, string name)
{
	dot_graph graph;
	graph.type = "digraph";
	graph.id = name;

	for (size_t i = 0; i < vars.globals.size(); i++)
	{
		graph.stmt_list.stmts.push_back(dot_stmt());
		dot_stmt &stmt = graph.stmt_list.stmts.back();
		stmt.stmt_type = "node";
		stmt.node_ids.push_back(dot_node_id("V" + to_string(i)));
		stmt.attr_list.attrs.push_back(dot_a_list());
		dot_a_list &attr = stmt.attr_list.attrs.back();
		attr.as.push_back(dot_a());
		dot_a &a = attr.as.back();
		a.first.id = "label";
		a.second.id = vars.globals[i].name;
	}

	map<pair<int, int>, pair<bool, bool> >::iterator net2iter;
	for (net2iter = bubble_net.begin(); net2iter != bubble_net.end(); net2iter++)
	{
		graph.stmt_list.stmts.push_back(dot_stmt());
		dot_stmt &stmt = graph.stmt_list.stmts.back();
		stmt.stmt_type = "edge";
		stmt.node_ids.push_back(dot_node_id("V" + to_string(net2iter->first.first)));
		stmt.node_ids.push_back(dot_node_id("V" + to_string(net2iter->first.second)));
		if (net2iter->second.first || net2iter->second.second)
		{
			stmt.attr_list.attrs.push_back(dot_a_list());
			dot_a_list &attr = stmt.attr_list.attrs.back();

			if (net2iter->second.first)
			{
				attr.as.push_back(dot_a());
				dot_a &a = attr.as.back();
				a.first.id = "style";
				a.second.id = "dashed";
			}

			if (net2iter->second.second)
			{
				attr.as.push_back(dot_a());
				dot_a &a1 = attr.as.back();
				a1.first.id = "arrowhead";
				a1.second.id = "odotnormal";
			}
		}
	}

	return graph;
}

void rule_space::print(variable_space &vars, ostream &fout, string newl)
{
	for (size_t i = 0; i < rules.size(); i++)
		if (vars.globals[i].written)
			rules[i].print(vars, fout, "");

	for (size_t i = 0; i < excl.size(); i++)
		if (excl[i].first.size() > 1)
		{
			fout << "mk_excl" << (excl[i].second == 0 ? "lo" : "hi") << "(";
			for (size_t j = 0; j < excl[i].first.size(); j++)
			{
				if (j != 0)
					fout << ",";
				fout << vars.globals[excl[i].first[j]].name;
			}
			fout << ")" << newl;
		}
}

*/
