#pragma once

#include <functional>   // std::greater
#include <algorithm>

#include "../settings.h"
#include "iterator.h"
#include "column-relation.h"

struct hist_bucket
{
	uint32_t frequency; // frequency of distinct values
	uint32_t distinct_values;
	uint64_t max_value;
	uint32_t max_value_frequency;
};

class MaxdiffHistogram
{
	std::vector<bool> isUnique;
	std::vector<hist_bucket*> histogram;
	std::vector<uint32_t> histogramCount;
public:
	void loadRelation(ColumnRelation& relation);

	uint32_t estimateResult(const Filter& filter);
};
