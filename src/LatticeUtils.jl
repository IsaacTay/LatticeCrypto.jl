using LinearAlgebra
using Base.Threads

using ProgressMeter

function norm2(v) # Optimisation over norm(v)^2
	return sum(v.^2)
end

function hadamard_ratio(m)
	d = size(m, 2)
	return (abs(det(BigInt.(m))) / prod(norm.(view.([m], :, 1:d))))^(1/d)
end

function mew(vi, vj)
    return (vi ⋅ vj)/(norm2(vj))
end

# Gram–Schmidt Orthogonal Basis
function gs_ortho(vi, vs)
    change = [Vector{Float64}(undef, size(vi)) for _ in 1:length(vs)]
    @threads for i in 1:length(vs)
        change[i] = mew(vi, vs[i]) * vs[i]
    end
    return vi - sum(change)
    # return vi - sum(@. mew.([vi], vs) .* vs)
end

# Lattice Reduction for 2 vectors
function lattice_reduction(v1, v2)
	while true
		if norm(v2) < norm(v1)
			v1, v2 = v2, v1
		end
		m = round.(Int, (v1 ⋅ v2)/norm(v1)^2)
		if m == 0
			return v1, v2
		else
			v2 -= m * v1
		end
	end
end

function LLL(v)
    # v::Vector{Vector{Int64}}
	n = size(v, 2)
    v = getindex.([v], :, 1:n)
	k = 2
	v_star = [Vector{Float64}(undef, size(v, 1)) for _ in 1:n]
    v_star[1] = v[1]
    count = 0
	while k <= n
		v_star[1] = v[1]
        for i = max(k-1, 2):k # Recalculates v* only for k-1 & k
            v_star[i] = @views gs_ortho(v[i], v_star[1:i-1])
        end
		for j = k-1:-1:1
			v[k] = @views v[k] - round(mew(v[k], v_star[j])) * v[j]
		end
		v_star[k] = @views gs_ortho(v[k], v_star[1:k-1])
        if @views norm2(v_star[k]) >= (3/4 - mew(v[k], v_star[k-1])^2) * norm2(v_star[k-1])
			k = k + 1
		else
            count += 1
			v[k-1], v[k] = v[k], v[k-1]
			k = max(k - 1, 2)
		end
	end
	finish!(p; showvalues = [(:steps, count)])
	return v
end

# Test functions

function test_LLL()
	M = [19 2 32 46 3 33;
	15 42 11 0 3 24;
	43 15 0 24 4 16;
	20 44 44 0 18 15;
	0 48 35 16 31 31;
	48 33 32 9 1 29]'

	return LLL(M)
end

function test_LLL2() # Knapsack func
    M = [2 0 0 0 0 89 ;
	0 2 0 0 0 243 ;
	0 0 2 0 0 212 ;
	0 0 0 2 0 150 ;
	0 0 0 0 2 245 ;
	1 1 1 1 1 546]'
    return LLL(M)
end

# test_LLL()
test_LLL2()
# @time for i = 1:1000 test_LLL2() end