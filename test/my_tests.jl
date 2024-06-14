using StochasticAD
using Test
using Distributions
using ForwardDiff
using OffsetArrays
using ChainRulesCore
using Random
using Zygote

#const backends = [
#    PrunedFIsBackend(),
#    PrunedFIsAggressiveBackend(),
#    DictFIsBackend(),
#]
#
#const backends_smoothed = [
#    SmoothedFIsBackend(),
#    StrategyWrapperFIsBackend(SmoothedFIsBackend(), StochasticAD.TwoSidedStrategy()),
#]
@testset "Test 2D array indexing" begin
    for backend in vcat(backends, backends_smoothed)
        p = 0.3
        # Test indexing into array of floats with stochastic triple index
        arr = [[3.5, 5.2, 8.4] [1.2, 4.5, 9.1]]
        # test index resp. to index 2
        (backend in backends_smoothed) && (arr[3, 1] = 6.9) # make linear for smoothing test
        function array_index_1(p)
            index = rand(Categorical([p / 2, p / 2, 1 - p]))
            return arr[index, 1]
        end
        array_index_mean(p) = sum([p / 2, p / 2, (1 - p)] .* arr)
        triple_array_index_deriv = mean(derivative_estimate(array_index_1, p; backend)
                                        for i in 1:50000)
        exact_array_index_deriv = ForwardDiff.derivative(array_index_mean, p)
        @test isapprox(triple_array_index_deriv, exact_array_index_deriv, rtol = 5e-2)
        return
        # Don't run subsequent tests with smoothing backend
        (backend in backends_smoothed) && continue
        # Test indexing into array of stochastic triples with stochastic triple index
        function array_index2(p)
            arr2 = [rand(Bernoulli(p)), rand(Bernoulli(p)), rand(Bernoulli(p))] .* arr
            index = rand(Categorical([p / 2, p / 2, 1 - p]))
            return arr2[index]
        end
        array_index2_mean(p) = sum([p / 2 * p, p / 2 * p, (1 - p) * p] .* arr)
        triple_array_index2_deriv = mean(derivative_estimate(array_index2, p; backend)
                                         for i in 1:50000)
        exact_array_index2_deriv = ForwardDiff.derivative(array_index2_mean, p)
        @test isapprox(triple_array_index2_deriv, exact_array_index2_deriv, rtol = 5e-2)
        # Test case where triple and alternate array value are coupled
        function array_index3(p)
            st = rand(Bernoulli(p))
            arr2 = [-5, st]
            return arr2[st + 1]
        end
        array_index3_mean(p) = -5 * (1 - p) + 1 * p
        triple_array_index3_deriv = mean(derivative_estimate(array_index3, p; backend)
                                         for i in 1:50000)
        exact_array_index3_deriv = ForwardDiff.derivative(array_index3_mean, p)
        @test isapprox(triple_array_index3_deriv, exact_array_index3_deriv, rtol = 5e-2)
    end
end