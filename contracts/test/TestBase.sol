// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

interface Vm {
    function warp(uint256 newTimestamp) external;
    function getBlockTimestamp() external view returns (uint256);
    function prank(address msgSender) external;
    function startPrank(address msgSender) external;
    function stopPrank() external;
    function expectRevert(bytes4 revertData) external;
}

/// @title Minimal Self-Contained Foundry Test Base
/// @notice Provides standard Foundry cheatcodes, assertions, and fuzz bounds without external git submodules.
abstract contract TestBase {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));

    function skip(uint256 _seconds) internal {
        vm.warp(vm.getBlockTimestamp() + _seconds);
    }

    event LogNamedUint(string key, uint256 val);
    event LogNamedInt(string key, int256 val);
    event LogNamedString(string key, string val);

    error AssertionFailed(string reason);

    function bound(uint256 x, uint256 min, uint256 max) internal pure returns (uint256 result) {
        if (min > max) revert AssertionFailed("bound: min > max");
        if (x >= min && x <= max) return x;
        uint256 size = max - min + 1;
        if (size == 0) return x;
        return min + (x % size);
    }

    function assertTrue(bool condition, string memory msgStr) internal pure {
        if (!condition) revert AssertionFailed(msgStr);
    }

    function assertEq(uint256 a, uint256 b, string memory msgStr) internal pure {
        if (a != b) revert AssertionFailed(msgStr);
    }

    function assertGt(uint256 a, uint256 b, string memory msgStr) internal pure {
        if (!(a > b)) revert AssertionFailed(msgStr);
    }

    function assertGe(uint256 a, uint256 b, string memory msgStr) internal pure {
        if (!(a >= b)) revert AssertionFailed(msgStr);
    }

    function assertLt(uint256 a, uint256 b, string memory msgStr) internal pure {
        if (!(a < b)) revert AssertionFailed(msgStr);
    }

    function assertLe(uint256 a, uint256 b, string memory msgStr) internal pure {
        if (!(a <= b)) revert AssertionFailed(msgStr);
    }

    function assertApproxEqAbs(uint256 a, uint256 b, uint256 maxDelta, string memory msgStr) internal pure {
        uint256 diff = a > b ? a - b : b - a;
        if (diff > maxDelta) revert AssertionFailed(msgStr);
    }
}
