// SPDX-License-Identifier: MIT
pragma solidity 0.8.24;

/// @title Minimal BOLD ERC20 Token
/// @notice Self-contained ERC20 implementation for stateful Liquity V2 mechanism benchmarks.
contract BoldToken {
    string public constant name = "BOLD";
    string public constant symbol = "BOLD";
    uint8 public constant decimals = 18;

    uint256 public totalSupply;
    address public immutable minter;

    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    error Unauthorized();
    error ZeroAddress();
    error InsufficientBalance();
    error InsufficientAllowance();

    event Transfer(address indexed from, address indexed to, uint256 value);
    event Approval(address indexed owner, address indexed spender, uint256 value);

    constructor(address _minter) {
        if (_minter == address(0)) revert ZeroAddress();
        minter = _minter;
    }

    function mint(address _to, uint256 _amount) external {
        if (msg.sender != minter) revert Unauthorized();
        totalSupply += _amount;
        unchecked {
            balanceOf[_to] += _amount;
        }
        emit Transfer(address(0), _to, _amount);
    }

    function burn(address _from, uint256 _amount) external {
        if (msg.sender != minter) revert Unauthorized();
        uint256 bal = balanceOf[_from];
        if (bal < _amount) revert InsufficientBalance();
        unchecked {
            balanceOf[_from] = bal - _amount;
            totalSupply -= _amount;
        }
        emit Transfer(_from, address(0), _amount);
    }

    function approve(address _spender, uint256 _amount) external returns (bool) {
        allowance[msg.sender][_spender] = _amount;
        emit Approval(msg.sender, _spender, _amount);
        return true;
    }

    function transfer(address _to, uint256 _amount) external returns (bool) {
        _transfer(msg.sender, _to, _amount);
        return true;
    }

    function transferFrom(address _from, address _to, uint256 _amount) external returns (bool) {
        if (msg.sender != minter) {
            uint256 allowed = allowance[_from][msg.sender];
            if (allowed != type(uint256).max) {
                if (allowed < _amount) revert InsufficientAllowance();
                unchecked {
                    allowance[_from][msg.sender] = allowed - _amount;
                }
            }
        }
        _transfer(_from, _to, _amount);
        return true;
    }

    function _transfer(address _from, address _to, uint256 _amount) internal {
        uint256 bal = balanceOf[_from];
        if (bal < _amount) revert InsufficientBalance();
        unchecked {
            balanceOf[_from] = bal - _amount;
            balanceOf[_to] += _amount;
        }
        emit Transfer(_from, _to, _amount);
    }
}
