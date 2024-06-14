"""
Operators which have already been overloaded by StochasticAD. 
"""
const handled_ops = Tuple{DataType, Int}[]

"""
	define_triple_overload(sig)

Given the signature type-type of the primal function, define operator
overloading rules for stochastic triples.
Currently supports functions with all-real inputs and one real output.
"""
# TODO: special case optimizations
# TODO: generalizations to not-all-real inputs and/or not-one-real output
function define_triple_overload(sig)
    opT, argTs = Iterators.peel(ExprTools.parameters(sig))
    opT <: Type{<:Type} && return  # not handling constructors
    sig <: Tuple{Type, Vararg{Any}} && return
    opT <: Core.Builtin && return false  # can't do operator overloading for builtins

    isabstracttype(opT) || fieldcount(opT) == 0 || return false  # not handling functors
    isempty(argTs) && return false  # we are an operator overloading AD, need operands
    all(argT isa Type && Real <: argT for argT in argTs) || return

    N = length(ExprTools.parameters(sig)) - 1  # skip the op

    # Skip already-handled ops, as well as ops that will be handled manually later (and more correctly, see #79).
    if (opT, N) in handled_ops || (opT.instance in UNARY_TYPEFUNCS_WRAP)
        return
    end

    push!(handled_ops, (opT, N))

    if opT.instance in UNARY_PREDICATES && (N == 1)
        @eval function (f::$opT)(st::StochasticTriple)
            val = value(st)
            out = f(val)
            if !alltrue(Δ -> (f(val + Δ) == out), st.Δs)
                error("Output of boolean predicate cannot depend on input (unsupported by StochasticAD)")
            end
            return out
        end
    elseif opT.instance in BINARY_PREDICATES && (N == 2)
        # Special case equality comparisons as in https://github.com/JuliaDiff/ForwardDiff.jl/pull/481
        if opT.instance == Base.:(==)
            return_value_real = quote
                out && iszero(delta(st))
            end
            return_value_st = quote
                out2 = out && (delta(st1) == delta(st2))
            end
        else
            return_value_real = quote
                out
            end
            return_value_st = quote
                out
            end
        end
        @eval function (f::$opT)(st::StochasticTriple, x::Real)
            val = value(st)
            out = f(val, x)
            if !alltrue(Δ -> (f(val + Δ, x) == out), st.Δs)
                error("Output of boolean predicate cannot depend on input (unsupported by StochasticAD)")
            end
            return $return_value_real
        end
        @eval function (f::$opT)(x::Real, st::StochasticTriple)
            val = value(st)
            out = f(x, val)
            if !alltrue(Δ -> (f(x, val + Δ) == out), st.Δs)
                error("Output of boolean predicate cannot depend on input (unsupported by StochasticAD)")
            end
            return $return_value_real
        end
        @eval function (f::$opT)(st1::StochasticTriple, st2::StochasticTriple)
            val1 = value(st1)
            val2 = value(st2)
            out = f(val1, val2)

            Δs_coupled = couple((st1.Δs, st2.Δs); out_rep = (val1, val2))
            safe_perturb = alltrue(Δs -> f(val1 + Δs[1], val2 + Δs[2]) == out, Δs_coupled)
            if !safe_perturb
                error("Output of boolean predicate cannot depend on input (unsupported by StochasticAD)")
            end
            return $return_value_st
        end
    elseif N == 1
        if Base.return_types(frule, (Tuple{NoTangent, Real}, opT, Real))[1] <:
           Tuple{Any, NoTangent}
            return
        end
        @eval function (f::$opT)(st::StochasticTriple{T}; kwargs...) where {T}
            run_frule = δ -> begin
                args_tangent = (NoTangent(), δ)
                return frule(args_tangent, f, value(st); kwargs...)
            end
            val, δ0 = run_frule(delta(st))
            δ::typeof(val) = (δ0 isa ZeroTangent || δ0 isa NoTangent) ? zero(value(st)) : δ0
            if !iszero(st.Δs)
                Δs = map(Δ -> f(st.value + Δ; kwargs...) - val, st.Δs;
                    deriv = last ∘ run_frule, out_rep = val)
            else
                Δs = similar_empty(st.Δs, typeof(val))
            end
            return StochasticTriple{T}(val, δ, Δs)
        end
    elseif N == 2
        if Base.return_types(frule, (Tuple{NoTangent, Real, Real}, opT, Real, Real))[1] <:
           Tuple{Any, NoTangent}
            return
        end
        for R in AMBIGUOUS_TYPES
            @eval function (f::$opT)(st::StochasticTriple{T}, x::$R; kwargs...) where {T}
                run_frule = δ -> begin
                    args_tangent = (NoTangent(), δ, zero(x))
                    return frule(args_tangent, f, value(st), x; kwargs...)
                end
                val, δ0 = run_frule(delta(st))
                δ::typeof(val) = (δ0 isa ZeroTangent || δ0 isa NoTangent) ?
                                 zero(value(st)) : δ0
                if !iszero(st.Δs)
                    Δs = map(Δ -> f(st.value + Δ, x; kwargs...) - val, st.Δs;
                        deriv = last ∘ run_frule, out_rep = val)
                else
                    Δs = similar_empty(st.Δs, typeof(val))
                end
                return StochasticTriple{T}(val, δ, Δs)
            end
            @eval function (f::$opT)(x::$R, st::StochasticTriple{T}; kwargs...) where {T}
                run_frule = δ -> begin
                    args_tangent = (NoTangent(), zero(x), δ)
                    return frule(args_tangent, f, x, value(st); kwargs...)
                end
                val, δ0 = run_frule(delta(st))
                δ::typeof(val) = (δ0 isa ZeroTangent || δ0 isa NoTangent) ?
                                 zero(value(st)) : δ0
                if !iszero(st.Δs)
                    Δs = map(Δ -> f(x, st.value + Δ; kwargs...) - val, st.Δs;
                        deriv = last ∘ run_frule, out_rep = val)
                else
                    Δs = similar_empty(st.Δs, typeof(val))
                end
                return StochasticTriple{T}(val, δ, Δs)
            end
        end
        @eval function (f::$opT)(sts::Vararg{StochasticTriple{T}, 2}; kwargs...) where {T}
            run_frule = δs -> begin
                args_tangent = (NoTangent(), δs...)
                args = (f, value.(sts)...)
                return frule(args_tangent, args...; kwargs...)
            end
            val, δ0 = run_frule(delta.(sts))
            δ::typeof(val) = (δ0 isa ZeroTangent || δ0 isa NoTangent) ? zero(value(st)) : δ0

            Δs_all = map(st -> getfield(st, :Δs), sts)
            if all(iszero.(Δs_all))
                Δs = similar_empty(first(sts).Δs, typeof(val))
            else
                vals_in = value.(sts)
                Δs_coupled = couple(Tuple(Δs_all); out_rep = vals_in)
                mapfunc = let vals_in = vals_in
                    Δ -> (f((vals_in .+ Δ)...; kwargs...) - val)
                end
                Δs = map(mapfunc, Δs_coupled; deriv = last ∘ run_frule, out_rep = val)
            end
            return StochasticTriple{T}(val, δ, Δs)
        end
    end
end

on_new_rule(define_triple_overload, frule)

### Extra overloads

# TODO: generalize the below logic to compactly handle a wider range of functions.
# See also https://github.com/JuliaDiff/ForwardDiff.jl/blob/master/src/dual.jl.

function Base.hash(st::StochasticTriple, hsh::UInt)
    if !isempty(st.Δs)
        error("Hashing a stochastic triple with perturbations not yet supported.")
    end
    hash(StochasticAD.value(st), hsh)
end

#=
This is a hacky experimental way to convert a float-like stochastic triple
into an integer-like one, to facilitate generic coding.
=#
function Base.round(I::Type{<:Integer}, st::StochasticTriple{T, V}) where {T, V}
    return StochasticTriple{T}(round(I, st.value), map(Δ -> round(I, st.value + Δ), st.Δs))
end

for op in UNARY_TYPEFUNCS_NOWRAP
    function (::typeof(op))(::Type{<:StochasticTriple{T, V, FIs}}) where {T, V, FIs}
        return op(V)
    end
end

for op in UNARY_TYPEFUNCS_WRAP
    function (::typeof(op))(::Type{StochasticTriple{T, V, FIs}}) where {T, V, FIs}
        return StochasticTriple{T, V, FIs}(op(V), zero(V), empty(FIs))
    end
    function (::typeof(op))(st::StochasticTriple)
        return op(typeof(st))
    end
end

for op in RNG_TYPEFUNCS_WRAP
    function (::typeof(op))(rng::AbstractRNG,
            ::Type{StochasticTriple{T, V, FIs}}) where {T, V, FIs}
        return StochasticTriple{T, V, FIs}(op(rng, V), zero(V), empty(FIs))
    end
end

#=
The short-circuit "x == y" case in Base.isapprox is bad for us
because it could unnecessarily lead to a boolean-predicate
depends on output error where StochasticAD cannot prove correctness.
We patch up the rule by removing the short-circuit, allowing some common
cases to work.

In the future, we will ideally handle the overloading rule in a more general
way. (E.g. by catching the chain rule for isapprox and recursively calling isapprox
on the values.)
=#
function Base.isapprox(st1::StochasticTriple, st2::StochasticTriple;
        atol::Real = 0, rtol::Real = Base.rtoldefault(st1, st2, atol),
        nans::Bool = false, norm::Function = abs)
    (isfinite(st1) && isfinite(st2) &&
     norm(st1 - st2) <= max(atol, rtol * max(norm(st1), norm(st2)))) ||
        (nans && isnan(st1) && isnan(st2))
end
function Base.isapprox(st1::StochasticTriple, x::Real;
        atol::Real = 0, rtol::Real = Base.rtoldefault(st1, x, atol),
        nans::Bool = false, norm::Function = abs)
    (isfinite(st1) && isfinite(x) &&
     norm(st1 - x) <= max(atol, rtol * max(norm(st1), norm(x)))) ||
        (nans && isnan(st1) && isnan(x))
end
function Base.isapprox(x::Real, st::StochasticTriple; kwargs...)
    return Base.isapprox(st, x; kwargs...)
end

# Alternate version of _isassigned that does not fall back on try/catch.
_isassigned(C, i) = (i in eachindex(C))

"""
	Base.getindex(C::AbstractArray, st::StochasticTriple{T})

A simple prototype rule for array indexing. Assumes that underlying type of `st` can index into collection C.
"""
# TODO: support multiple indices, cartesian indices, non abstract array indexables, other use cases...
# Example to fix: A[:, :, st]
function Base.getindex(C::AbstractArray, st::StochasticTriple{T, V, FIs}) where {T, V, FIs}
    val = C[st.value]
    do_map = (Δ, state) -> begin
        return value(C[st.value + Δ], state) - value(val, state)
    end

    # TODO: below doesn't support sparse arrays, use something like nextind
    deriv = δ -> begin
        scale = if _isassigned(C, st.value + 1) && _isassigned(C, st.value - 1)
            1 / 2 * (value(C[st.value + 1]) - value(C[st.value - 1]))
        elseif _isassigned(C, st.value + 1)
            value(C[st.value + 1]) - value(C[st.value])
        elseif _isassigned(C, st.value - 1)
            value(C[st.value]) - value(C[st.value - 1])
        else
            zero(eltype(C))
        end
        return scale * δ
    end

    Δs = StochasticAD.map_Δs(do_map, st.Δs; deriv, out_rep = value(val))
    if val isa StochasticTriple
        Δs = combine((Δs, val.Δs))
    end
    return StochasticTriple{T}(value(val), delta(val), Δs)
end

function Base.getindex(
        C::AbstractArray, st::StochasticTriple{T, V, FIs}, i2) where {T, V, FIs}
    val = C[st.value, i2]
    do_map = (Δ, state) -> begin
        return value(C[st.value + Δ, i2], state) - value(val, state)
    end
    is_assigned(C, i) = 1 <= i <= size(C, 1)
    # TODO: below doesn't support sparse arrays, use something like nextind
    deriv = δ -> begin
        scale = if is_assigned(C, st.value + 1) && is_assigned(C, st.value - 1)
            1 / 2 * (value(C[st.value + 1, i2]) - value(C[st.value - 1, i2]))
        elseif is_assigned(C, st.value + 1)
            value(C[st.value + 1, i2]) - value(C[st.value, i2])
        elseif is_assigned(C, st.value - 1)
            value(C[st.value, i2]) - value(C[st.value - 1, i2])
        else
            zero(eltype(C))
        end
        return scale * δ
    end

    Δs = StochasticAD.map_Δs(do_map, st.Δs; deriv, out_rep = value(val))
    if val isa StochasticTriple
        Δs = combine((Δs, val.Δs))
    end
    return StochasticTriple{T}(value(val), delta(val), Δs)
end

function Base.getindex(
        C::AbstractArray, i1, st::StochasticTriple{T, V, FIs}) where {T, V, FIs}
    val = C[i1, st.value]
    do_map = (Δ, state) -> begin
        return value(C[i1, st.value + Δ], state) - value(val, state)
    end
    is_assigned(C, i) = 1 <= i <= size(C, 2)
    # TODO: below doesn't support sparse arrays, use something like nextind
    deriv = δ -> begin
        scale = if is_assigned(C, st.value + 1) && is_assigned(C, st.value - 1)
            1 / 2 * (value(C[i1, st.value + 1]) - value(C[i1, st.value - 1]))
        elseif is_assigned(C, st.value + 1)
            value(C[i1, st.value + 1]) - value(C[i1, st.value])
        elseif is_assigned(C, st.value - 1)
            value(C[i1, st.value]) - value(C[i1, st.value - 1])
        else
            zero(eltype(C))
        end
        return scale * δ
    end

    Δs = StochasticAD.map_Δs(do_map, st.Δs; deriv, out_rep = value(val))
    if val isa StochasticTriple
        Δs = combine((Δs, val.Δs))
    end
    return StochasticTriple{T}(value(val), delta(val), Δs)
end

function Base.getindex(C::AbstractArray, i1::StochasticTriple{T, V, FIs},
        i2::StochasticTriple{T, V, FIs}) where {T, V, FIs}
    val = C[i1.value, i2.value]
    do_map_1 = (Δ, state) -> begin
        return value(C[i1.value + Δ, i2.value], state) - value(val, state)
    end
    do_map_2 = (Δ, state) -> begin
        return value(C[i1.value, i2.value + Δ], state) - value(val, state)
    end
    is_assigned_1(C, i) = 1 <= i <= size(C, 1)
    is_assigned_2(C, i) = 1 <= i <= size(C, 2)
    # TODO: below doesn't support sparse arrays, use something like nextind
    deriv_1 = δ -> begin
        scale = if is_assigned_1(C, i1.value + 1) && is_assigned_1(C, i1.value - 1)
            1 / 2 * (value(C[i1.value + 1, i2.value]) - value(C[i1.value - 1, i2.value]))
        elseif is_assigned_1(C, i1.value + 1)
            value(C[i1.value + 1, i2.value]) - value(C[i1.value, i2.value])
        elseif is_assigned_1(C, st.value - 1)
            value(C[i1.value, i2.value]) - value(C[i1.value - 1, i2.value])
        else
            zero(eltype(C))
        end
        return scale * δ
    end
    deriv_2 = δ -> begin
        scale = if is_assigned_2(C, i2.value + 1) && is_assigned_2(C, i2.value - 1)
            1 / 2 * (value(C[i1.value, i2.value + 1]) - value(C[i1.value, i2.value - 1]))
        elseif is_assigned_2(C, i2.value + 1)
            value(C[i1.value, i2.value + 1]) - value(C[i1.value, i2.value])
        elseif is_assigned_2(C, i2.value - 1)
            value(C[i1.value, i2.value]) - value(C[i1.value, i2.value - 1])
        else
            zero(eltype(C))
        end
        return scale * δ
    end

    Δs_1 = StochasticAD.map_Δs(do_map_1, i1.Δs; deriv_1, out_rep = value(val))
    Δs_2 = StochasticAD.map_Δs(do_map_2, i2.Δs; deriv_2, out_rep = value(val))
    # randomly choose one of the two to be the "main" perturbation. Should be weighted by their relative weight
    w1 = Δs_1.state.weight
    w2 = Δs_2.state.weight
    if rand() < w1 / (w1 + w2)
        Δs = Δs_1
    else
        Δs = Δs_2
    end
    #Δs = combine((Δs_1, Δs_2))
    if val isa StochasticTriple
        Δs = combine((Δs, val.Δs))
    end
    return StochasticTriple{T}(value(val), delta(val), Δs)
end

function Base.getindex(
        C::AbstractArray, i1::StochasticTriple{T, V, FIs}, i2::Colon) where {T, V, FIs}
    [C[i1, i] for i in 1:size(C, 2)]
end
function Base.getindex(
        C::AbstractArray, i1::Colon, i2::StochasticTriple{T, V, FIs}) where {T, V, FIs}
    [C[i, i2] for i in 1:size(C, 1)]
end
function Base.getindex(C::AbstractArray, i1::Colon,
        i2::Array{<:StochasticTriple{T, V, FIs}}) where {T, V, FIs}
    return [C[i1, i] for i in i2]
end
function Base.getindex(C::AbstractArray, i1::Array{<:StochasticTriple{T, V, FIs}},
        i2::Colon) where {T, V, FIs}
    return [C[i, i2] for i in i1]
end

## old ##
#function Base.getindex(C::AbstractArray, i1::StochasticTriple{T, V, FIs}, i2) where {T, V, FIs}
#	i1_value = value(i1)
#	val = C[i1_value, i2]
#	function do_map(Δ, state)
#		return value(C[i1_value+Δ, i2], state) - value(val, state)
#	end
#	Δs = map_Δs(do_map, i1.Δs)
#	if val isa StochasticTriple
#		Δs = combine((Δs, val.Δs))
#	end
#	return StochasticTriple{T}(value(val), delta(val), Δs)
#end
#function Base.getindex(C::AbstractArray, i1::StochasticTriple{T, V, FIs}, i2::StochasticTriple{T, V, FIs}) where {T, V, FIs}
#	i1_value = value(i1)
#    i2_value = value(i2)
#	val = C[i1_value, i2_value]
#	function do_map_i1(Δ, state)
#		return value(C[i1_value+Δ, i2_value], state) - value(val, state)
#	end
#	function do_map_i2(Δ, state)
#		return value(C[i1_value, i2_value + Δ], state) - value(val, state)
#	end
#	Δs = combine((map_Δs(do_map_i1, i1.Δs), map_Δs(do_map_i2, i2.Δs)))
#	if val isa StochasticTriple
#		Δs = combine((Δs, val.Δs))
#	end
#	return StochasticTriple{T}(value(val), delta(val), Δs)
#end
#Base.getindex(C::AbstractArray, i1::StochasticTriple{T, V, FIs}, i2::Colon) where {T, V, FIs} = [C[i1, i] for i in 1:size(C, 2)]
#Base.getindex(C::AbstractArray, i1::Colon, i2::StochasticTriple{T, V, FIs}) where {T, V, FIs} = [C[i, i2] for i in 1:size(C, 1)]
#function Base.getindex(C::AbstractArray, i1, i2::StochasticTriple{T, V, FIs}) where {T, V, FIs}
#	i2_value = value(i2)
#	val = C[i1, i2_value]
#	function do_map(Δ, state)
#		return value(C[i1, i2_value+Δ], state) - value(val, state)
#	end
#	Δs = StochasticAD.map_Δs(do_map, i2.Δs)
#	if val isa StochasticTriple
#		Δs = combine((Δs, val.Δs))
#	end
#	return StochasticTriple{T}(value(val), delta(val), Δs)
#end
#function Base.getindex(C::AbstractArray, i1::Colon, i2::Array{<:StochasticTriple{T, V, FIs}}) where {T, V, FIs}
#	return [C[i1, i] for i in i2]
#end
#function Base.getindex(C::AbstractArray, i1::Array{<:StochasticTriple{T, V, FIs}}, i2::Colon) where {T, V, FIs}
#	return [C[i, i2] for i in i1]
#end
#