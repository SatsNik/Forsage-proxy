/**
 *Submitted for verification at testnet.bscscan.com on 2024-11-29
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-11-26
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-11-12
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-19
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-17
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-16
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-15
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-15
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-13
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-10
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-04
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-10-02
*/

/**
 *Submitted for verification at BscScan.com on 2021-05-31
*/

// SPDX-License-Identifier: MIT

pragma solidity ^0.6.0;
pragma experimental ABIEncoderV2;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
 interface ISecondaryFeeHandler {
    function handleFeeAndSwap(address user, uint256 amount) external;
}
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}


/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
 

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
       // require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}


/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}



/**
 * @dev This abstract contract provides a fallback function that delegates all calls to another contract using the EVM
 * instruction `delegatecall`. We refer to the second contract as the _implementation_ behind the proxy, and it has to
 * be specified by overriding the virtual {_implementation} function.
 * 
 * Additionally, delegation to the implementation can be triggered manually through the {_fallback} function, or to a
 * different contract through the {_delegate} function.
 * 
 * The success and return data of the delegated call will be returned back to the caller of the proxy.
 */
abstract contract Proxy {
    /**
     * @dev Delegates the current call to `implementation`.
     * 
     * This function does not return to its internall call site, it will return directly to the external caller.
     */
    function _delegate(address implementation) internal {
        // solhint-disable-next-line no-inline-assembly
        assembly {
            // Copy msg.data. We take full control of memory in this inline assembly
            // block because it will not return to Solidity code. We overwrite the
            // Solidity scratch pad at memory position 0.
            calldatacopy(0, 0, calldatasize())

            // Call the implementation.
            // out and outsize are 0 because we don't know the size yet.
            let result := delegatecall(gas(), implementation, 0, calldatasize(), 0, 0)

            // Copy the returned data.
            returndatacopy(0, 0, returndatasize())

            switch result
            // delegatecall returns 0 on error.
            case 0 { revert(0, returndatasize()) }
            default { return(0, returndatasize()) }
        }
    }

    /**
     * @dev This is a virtual function that should be overriden so it returns the address to which the fallback function
     * and {_fallback} should delegate.
     */
    function _implementation() internal virtual view returns (address);

    /**
     * @dev Delegates the current call to the address returned by `_implementation()`.
     * 
     * This function does not return to its internall call site, it will return directly to the external caller.
     */
    function _fallback() internal {
        _beforeFallback();
        _delegate(_implementation());
    }

    /**
     * @dev Fallback function that delegates calls to the address returned by `_implementation()`. Will run if no other
     * function in the contract matches the call data.
     */
    fallback () payable external {
        _fallback();
    }

    /**
     * @dev Fallback function that delegates calls to the address returned by `_implementation()`. Will run if call data
     * is empty.
     */
    receive () payable external {
        _fallback();
    }

    /**
     * @dev Hook that is called before falling back to the implementation. Can happen as part of a manual `_fallback`
     * call, or as part of the Solidity `fallback` or `receive` functions.
     * 
     * If overriden should call `super._beforeFallback()`.
     */
    function _beforeFallback() internal virtual {
    }
}

contract ForsageProxy is Proxy {
    
    address public impl;
    address public contractOwner;

    modifier onlyContractOwner() { 
        require(msg.sender == contractOwner); 
        _; 
    }

    constructor(address _impl) public {
        impl = _impl;
        contractOwner = msg.sender;
    }
    
    function update(address newImpl) public onlyContractOwner {
        impl = newImpl;
    }

    function removeOwnership() public onlyContractOwner {
        contractOwner = address(0);
    }
    
    function _implementation() internal override view returns (address) {
        return impl;
    }
}


contract SmartMatrixForsageBasic {

  
    address public impl;
    address public contractOwner;



    struct User {
        uint id;
        address referrer;
        uint partnersCount;
        uint256 registrationTime;

        mapping(uint8 => bool) activeX3Levels;
        mapping(uint8 => bool) activeX6Levels;
        
        mapping(uint8 => X3) x3Matrix;
        mapping(uint8 => X6) x6Matrix;
    }
    struct CycleInfo {
    uint256[] completionTime;
    address[] participants;
}
    
struct X3 {
    address currentReferrer;
    address[] referrals;
    uint256[] entrytime;
    bool blocked;
    uint reinvestCount;
    CycleInfo[] cycles;
}

struct X6 {
    address currentReferrer;
    address[] firstLevelReferrals;
    address[] secondLevelReferrals;
    uint256[] firstentrytime;
    uint256[] secondentrytime;
    bool blocked;
    uint reinvestCount;
    address closedPart;
    CycleInfo[] cycles;
}
   event X3CycleCompleted(address indexed user, uint8 level, uint256 cycleIndex);
    event X6CycleCompleted(address indexed user, uint8 level, uint256 cycleIndex);


    uint8 public LAST_LEVEL;
    
    mapping(address => User) public users;
    mapping(uint => address) public idToAddress;
    mapping(uint => address) public userIds;
    mapping(address => uint) public balances; 

    uint public lastUserId;
    address public id1;
    address public multisig;
     mapping(address => mapping(uint8 => mapping(uint8 => mapping(address => bool)))) public allDirectPartners;
    mapping(uint8 => uint) public levelPrice;

    IERC20 public depositToken;
    
    uint public BASIC_PRICE;

    bool public locked;
    
    event Registration(address indexed user, address indexed referrer, uint indexed userId, uint referrerId);
    event Reinvest(address indexed user, address indexed currentReferrer, address indexed caller, uint8 matrix, uint8 level);
    event Upgrade(address indexed user, address indexed referrer, uint8 matrix, uint8 level);
    event NewUserPlace(address indexed user, address indexed referrer, uint8 matrix, uint8 level, uint8 place);
    event MissedEthReceive(address indexed receiver, address indexed from, uint8 matrix, uint8 level);
    event SentExtraEthDividends(address indexed from, address indexed receiver, uint8 matrix, uint8 level);
}

contract SmartMatrixForsage is SmartMatrixForsageBasic {
       struct RecentActivity {
        uint256 timestamp;
        uint256 userId;
        ActivityType activityType;
        uint8 matrix;
        uint8 level;
    }
    
    enum ActivityType { Registration, LevelPurchase }

   uint256 internal constant REGISTRATION_EXTRA_FEE = 2e18; // Total remains 2 BUSD
    uint256 internal constant REGISTRATION_PRIMARY_FEE = 17e17; // 1.7 BUSD to fee collector
    uint256 internal constant REGISTRATION_SECONDARY_FEE = 3e17; // 0.3 BUSD to secondary

    uint256 internal constant LEVEL_EXTRA_FEE = 4e18; // Total remains 4 BUSD
    uint256 internal constant LEVEL_PRIMARY_FEE = 34e17; // 3.4 BUSD to fee collector
    uint256 internal constant LEVEL_SECONDARY_FEE = 6e17; // 0.6 BUSD to secondary

    // CHANGE: Update the fee collector declarations
    address internal feeCollector;
    ISecondaryFeeHandler public secondaryFeeHandler; 
   
    

    // Array to store recent activities
    RecentActivity[] private recentActivities;
    using SafeERC20 for IERC20;

    struct UserMatrixDetails {
    uint256 userId;
    address userAddress;
    uint256 timestamp;
    uint8 matrix;
    uint8 level;
    string userType;      // "Normal" or "Recycled"
    uint256 cycleNumber;  // 0 for normal, cycle number for recycled
    uint256 tokenAmount;  // Actual amount for normal, "recycled" for cycle completions
}


    modifier onlyContractOwner() { 
        require(msg.sender == contractOwner, ""); 
        _; 
    }

    modifier onlyUnlocked() { 
        require(!locked || msg.sender == contractOwner); 
        _; 
    }
    
     function init(
        address _ownerAddress, 
        address _multisig, 
        IERC20 _depositTokenAddress,
        address _feeCollector,
        address _secondaryHandler
    ) public onlyContractOwner {
        require(_feeCollector != address(0), "");
        require(_secondaryHandler != address(0), "");


          BASIC_PRICE = 5e18;
        LAST_LEVEL = 12;
        levelPrice[1] = BASIC_PRICE;
        for (uint8 i = 2; i <= 8; i++) {
            levelPrice[i] = levelPrice[i-1] * 2;
        }
        levelPrice[9] = 1250e18;
        levelPrice[10] = 2500e18;
        levelPrice[11] = 5000e18;
        levelPrice[12] = 9900e18;
        
        id1 = _ownerAddress;
        feeCollector = _feeCollector;
        secondaryFeeHandler = ISecondaryFeeHandler(_secondaryHandler);

        User memory user = User({
            id: 1,
            referrer: address(0),
            partnersCount: uint(0),
            registrationTime: block.timestamp
        });
        
        users[_ownerAddress] = user;
        idToAddress[1] = _ownerAddress;
        
        for (uint8 i = 1; i <= LAST_LEVEL; i++) {
            users[_ownerAddress].activeX3Levels[i] = true;
            users[_ownerAddress].activeX6Levels[i] = true;
        }
        
        userIds[1] = _ownerAddress;
        lastUserId = 2;
        multisig = _multisig;

        depositToken = _depositTokenAddress;
        depositToken.approve(_secondaryHandler, type(uint256).max);
        locked = true;
    }

    function changeLock() external onlyContractOwner() {
        locked = !locked;
    }
    
    fallback() external {
        if(msg.data.length == 0) {
            return registration(msg.sender, id1);
        }
        
        registration(msg.sender, bytesToAddress(msg.data));
    }

    function registrationExt(address referrerAddress) external  onlyUnlocked() {
        registration(msg.sender, referrerAddress);
    }

    function registrationFor(address userAddress, address referrerAddress) external   onlyUnlocked() {
        registration(userAddress, referrerAddress);
    }
    
    function buyNewLevel(uint8 matrix, uint8 level) external  onlyUnlocked() {
        _buyNewLevel(msg.sender, matrix, level);
    }

    function buyNewLevelFor(address userAddress, uint8 matrix, uint8 level) external  onlyUnlocked() {
        _buyNewLevel(userAddress, matrix, level);
    }

    function _buyNewLevel(address _userAddress, uint8 matrix, uint8 level) internal {
        require(isUserExists(_userAddress), "");
        require(matrix == 1 || matrix == 2, "");

        uint256 totalAmount = levelPrice[level] + LEVEL_EXTRA_FEE;
        
        // Transfer total amount to contract first
        depositToken.safeTransferFrom(msg.sender, address(this), totalAmount);
        
        // Split and send fees
        depositToken.safeTransfer(feeCollector, LEVEL_PRIMARY_FEE);
        secondaryFeeHandler.handleFeeAndSwap(_userAddress, LEVEL_SECONDARY_FEE);
        
        // require(msg.value == levelPrice[level], "invalid price");
        require(level > 1 && level <= LAST_LEVEL, "");
         recentActivities.push(RecentActivity({
            timestamp: block.timestamp,
            userId: users[_userAddress].id,
            activityType: ActivityType.LevelPurchase,
            matrix: matrix,
            level: level
        }));

        if (matrix == 1) {
          require(users[_userAddress].activeX3Levels[level-1], "");
          require(!users[_userAddress].activeX3Levels[level], "");

            if (users[_userAddress].x3Matrix[level-1].blocked) {
                users[_userAddress].x3Matrix[level-1].blocked = false;
            }
    
            address freeX3Referrer = findFreeX3Referrer(_userAddress, level);
            users[_userAddress].x3Matrix[level].currentReferrer = freeX3Referrer;
            users[_userAddress].activeX3Levels[level] = true;
            updateX3Referrer(_userAddress, freeX3Referrer, level);
            
            emit Upgrade(_userAddress, freeX3Referrer, 1, level);

        } else {
            require(users[_userAddress].activeX6Levels[level-1], "");
            require(!users[_userAddress].activeX6Levels[level], ""); 

            if (users[_userAddress].x6Matrix[level-1].blocked) {
                users[_userAddress].x6Matrix[level-1].blocked = false;
            }

            address freeX6Referrer = findFreeX6Referrer(_userAddress, level);
            
            users[_userAddress].activeX6Levels[level] = true;
            updateX6Referrer(_userAddress, freeX6Referrer, level);
            
            emit Upgrade(_userAddress, freeX6Referrer, 2, level);
        }
    }
    
    function registration(address userAddress, address referrerAddress) private {
         uint256 totalAmount = (BASIC_PRICE * 2) + REGISTRATION_EXTRA_FEE;
        
        // Transfer total amount to contract first
        depositToken.safeTransferFrom(msg.sender, address(this), totalAmount);
        
        // Send extra fee to fee collector
         depositToken.safeTransfer(feeCollector, REGISTRATION_PRIMARY_FEE);
        secondaryFeeHandler.handleFeeAndSwap(userAddress, REGISTRATION_SECONDARY_FEE);

        // require(msg.value == BASIC_PRICE * 2, "invalid registration value");
         
        require(!isUserExists(userAddress), "user exists");
        require(isUserExists(referrerAddress), "referrer not exists");
        
        uint32 size;
        assembly {
            size := extcodesize(userAddress)
        }
        require(size == 0, "cannot be a contract");
        
        User memory user = User({
            id: lastUserId,
            referrer: referrerAddress,
            partnersCount: 0,
            registrationTime: block.timestamp
        });
     
        users[userAddress] = user;
        idToAddress[lastUserId] = userAddress;
        
        users[userAddress].referrer = referrerAddress;
        
        users[userAddress].activeX3Levels[1] = true; 
        users[userAddress].activeX6Levels[1] = true;
        
        
        userIds[lastUserId] = userAddress;
          recentActivities.push(RecentActivity({
            timestamp: block.timestamp,
            userId: lastUserId,  // Use lastUserId here
            activityType: ActivityType.Registration,
            matrix: 0,
            level: 0
        }));
        lastUserId++;
        
        users[referrerAddress].partnersCount++;

        address freeX3Referrer = findFreeX3Referrer(userAddress, 1);
        users[userAddress].x3Matrix[1].currentReferrer = freeX3Referrer;
        updateX3Referrer(userAddress, freeX3Referrer, 1);

        updateX6Referrer(userAddress, findFreeX6Referrer(userAddress, 1), 1);
        
        emit Registration(userAddress, referrerAddress, users[userAddress].id, users[referrerAddress].id);
    }
    function getUserRegistrationMetrics(uint256 time, string memory unit) public view returns (uint256 totalUsers, uint256 recentUsers) {
     totalUsers = lastUserId - 1; 

    uint256 secondsAgo;
    if (keccak256(bytes(unit)) == keccak256(bytes("sec"))) {
        secondsAgo = time;
    } else if (keccak256(bytes(unit)) == keccak256(bytes("min"))) {
        secondsAgo = time * 60;
    } else if (keccak256(bytes(unit)) == keccak256(bytes("hour"))) {
        secondsAgo = time * 3600;
    } else {
        revert("Invalid time unit. Use 'sec', 'min', or 'hour'");
    }

    uint256 cutoffTime = block.timestamp - secondsAgo;
    
    for (uint256 i = 1; i < lastUserId; i++) {
        if (users[userIds[i]].registrationTime > cutoffTime) {
            recentUsers++;
        }
    }

    return (totalUsers, recentUsers);
}
    
   function updateX3Referrer(address userAddress, address referrerAddress, uint8 level) private {
    users[referrerAddress].x3Matrix[level].referrals.push(userAddress);
    users[referrerAddress].x3Matrix[level].entrytime.push(block.timestamp);
    allDirectPartners[referrerAddress][1][level][userAddress] = true;
    if (users[referrerAddress].x3Matrix[level].referrals.length < 3) {
        emit NewUserPlace(userAddress, referrerAddress, 1, level, uint8(users[referrerAddress].x3Matrix[level].referrals.length));
        return sendETHDividends(referrerAddress, userAddress, 1, level);
    }
    
    emit NewUserPlace(userAddress, referrerAddress, 1, level, 3);
    
    // Record cycle completion
    uint256 cycleIndex = users[referrerAddress].x3Matrix[level].cycles.length;
    users[referrerAddress].x3Matrix[level].cycles.push(CycleInfo({
        completionTime: users[referrerAddress].x3Matrix[level].entrytime,
        participants: users[referrerAddress].x3Matrix[level].referrals
    }));
    
    emit X3CycleCompleted(referrerAddress, level, cycleIndex);
    
    //close matrix
    users[referrerAddress].x3Matrix[level].referrals = new address[](0);
    users[referrerAddress].x3Matrix[level].entrytime = new uint256[](0);
    if (!users[referrerAddress].activeX3Levels[level+1] && level != LAST_LEVEL) {
        users[referrerAddress].x3Matrix[level].blocked = true;
    }
        //create new one by recursion
        if (referrerAddress != id1) {
            //check referrer active level
            address freeReferrerAddress = findFreeX3Referrer(referrerAddress, level);
            if (users[referrerAddress].x3Matrix[level].currentReferrer != freeReferrerAddress) {
                users[referrerAddress].x3Matrix[level].currentReferrer = freeReferrerAddress;
            }
            
            users[referrerAddress].x3Matrix[level].reinvestCount++;
            emit Reinvest(referrerAddress, freeReferrerAddress, userAddress, 1, level);
            updateX3Referrer(referrerAddress, freeReferrerAddress, level);
        } else {
            sendETHDividends(id1, userAddress, 1, level);
            users[id1].x3Matrix[level].reinvestCount++;
            emit Reinvest(id1, address(0), userAddress, 1, level);
        }
    }

    function updateX6Referrer(address userAddress, address referrerAddress, uint8 level) private {
        require(users[referrerAddress].activeX6Levels[level], "500. Referrer level is inactive");
        
        if (users[referrerAddress].x6Matrix[level].firstLevelReferrals.length < 2) {
            users[referrerAddress].x6Matrix[level].firstLevelReferrals.push(userAddress);
            users[referrerAddress].x6Matrix[level].firstentrytime.push(block.timestamp);
            emit NewUserPlace(userAddress, referrerAddress, 2, level, uint8(users[referrerAddress].x6Matrix[level].firstLevelReferrals.length));
              allDirectPartners[referrerAddress][2][level][userAddress] = true;
            //set current level
            users[userAddress].x6Matrix[level].currentReferrer = referrerAddress;

            if (referrerAddress == id1) {
                return sendETHDividends(referrerAddress, userAddress, 2, level);
            }
            
            address ref = users[referrerAddress].x6Matrix[level].currentReferrer;            
            users[ref].x6Matrix[level].secondLevelReferrals.push(userAddress); 
            users[ref].x6Matrix[level].secondentrytime.push(block.timestamp); 
            uint len = users[ref].x6Matrix[level].firstLevelReferrals.length;
            
            if ((len == 2) && 
                (users[ref].x6Matrix[level].firstLevelReferrals[0] == referrerAddress) &&
                (users[ref].x6Matrix[level].firstLevelReferrals[1] == referrerAddress)) {
                if (users[referrerAddress].x6Matrix[level].firstLevelReferrals.length == 1) {
                    emit NewUserPlace(userAddress, ref, 2, level, 5);
                } else {
                    emit NewUserPlace(userAddress, ref, 2, level, 6);
                }
            }  else if ((len == 1 || len == 2) &&
                    users[ref].x6Matrix[level].firstLevelReferrals[0] == referrerAddress) {
                if (users[referrerAddress].x6Matrix[level].firstLevelReferrals.length == 1) {
                    emit NewUserPlace(userAddress, ref, 2, level, 3);
                } else {
                    emit NewUserPlace(userAddress, ref, 2, level, 4);
                }
            } else if (len == 2 && users[ref].x6Matrix[level].firstLevelReferrals[1] == referrerAddress) {
                if (users[referrerAddress].x6Matrix[level].firstLevelReferrals.length == 1) {
                    emit NewUserPlace(userAddress, ref, 2, level, 5);
                } else {
                    emit NewUserPlace(userAddress, ref, 2, level, 6);
                }
            }

            return updateX6ReferrerSecondLevel(userAddress, ref, level);
        }
        
        users[referrerAddress].x6Matrix[level].secondLevelReferrals.push(userAddress);
        users[referrerAddress].x6Matrix[level].secondentrytime.push(block.timestamp);
       allDirectPartners[referrerAddress][2][level][userAddress] = true;

        if (users[referrerAddress].x6Matrix[level].closedPart != address(0)) {
            if ((users[referrerAddress].x6Matrix[level].firstLevelReferrals[0] == 
                users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]) &&
                (users[referrerAddress].x6Matrix[level].firstLevelReferrals[0] ==
                users[referrerAddress].x6Matrix[level].closedPart)) {

                updateX6(userAddress, referrerAddress, level, true);
                return updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
            } else if (users[referrerAddress].x6Matrix[level].firstLevelReferrals[0] == 
                users[referrerAddress].x6Matrix[level].closedPart) {
                updateX6(userAddress, referrerAddress, level, true);
                return updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
            } else {
                updateX6(userAddress, referrerAddress, level, false);
                return updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
            }
        }

        if (users[referrerAddress].x6Matrix[level].firstLevelReferrals[1] == userAddress) {
            updateX6(userAddress, referrerAddress, level, false);
            return updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
        } else if (users[referrerAddress].x6Matrix[level].firstLevelReferrals[0] == userAddress) {
            updateX6(userAddress, referrerAddress, level, true);
            return updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
        }
        
        if (users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[0]].x6Matrix[level].firstLevelReferrals.length <= 
            users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]].x6Matrix[level].firstLevelReferrals.length) {
            updateX6(userAddress, referrerAddress, level, false);
        } else {
            updateX6(userAddress, referrerAddress, level, true);
        }
        
        updateX6ReferrerSecondLevel(userAddress, referrerAddress, level);
    }

    function updateX6(address userAddress, address referrerAddress, uint8 level, bool x2) private {
        if (!x2) {
            users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[0]].x6Matrix[level].firstLevelReferrals.push(userAddress);
            users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[0]].x6Matrix[level].firstentrytime.push(block.timestamp);
            emit NewUserPlace(userAddress, users[referrerAddress].x6Matrix[level].firstLevelReferrals[0], 2, level, uint8(users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[0]].x6Matrix[level].firstLevelReferrals.length));
            emit NewUserPlace(userAddress, referrerAddress, 2, level, 2 + uint8(users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[0]].x6Matrix[level].firstLevelReferrals.length));
            //set current level
            users[userAddress].x6Matrix[level].currentReferrer = users[referrerAddress].x6Matrix[level].firstLevelReferrals[0];
        } else {
            users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]].x6Matrix[level].firstLevelReferrals.push(userAddress);
            users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]].x6Matrix[level].firstentrytime.push(block.timestamp);
            emit NewUserPlace(userAddress, users[referrerAddress].x6Matrix[level].firstLevelReferrals[1], 2, level, uint8(users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]].x6Matrix[level].firstLevelReferrals.length));
            emit NewUserPlace(userAddress, referrerAddress, 2, level, 4 + uint8(users[users[referrerAddress].x6Matrix[level].firstLevelReferrals[1]].x6Matrix[level].firstLevelReferrals.length));
            //set current level
            users[userAddress].x6Matrix[level].currentReferrer = users[referrerAddress].x6Matrix[level].firstLevelReferrals[1];
        }
    }
    
    function updateX6ReferrerSecondLevel(address userAddress, address referrerAddress, uint8 level) private {
        if (users[referrerAddress].x6Matrix[level].secondLevelReferrals.length < 4) {
            return sendETHDividends(referrerAddress, userAddress, 2, level);
        }
      
        address[] memory x6 = users[users[referrerAddress].x6Matrix[level].currentReferrer].x6Matrix[level].firstLevelReferrals;
        
        if (x6.length == 2) {
            if (x6[0] == referrerAddress ||
                x6[1] == referrerAddress) {
                users[users[referrerAddress].x6Matrix[level].currentReferrer].x6Matrix[level].closedPart = referrerAddress;
            } else if (x6.length == 1) {
                if (x6[0] == referrerAddress) {
                    users[users[referrerAddress].x6Matrix[level].currentReferrer].x6Matrix[level].closedPart = referrerAddress;
                }
            }
        }
          uint256 cycleIndex = users[referrerAddress].x6Matrix[level].cycles.length;
          address[] memory allParticipants = new address[](
        users[referrerAddress].x6Matrix[level].firstLevelReferrals.length +
        users[referrerAddress].x6Matrix[level].secondLevelReferrals.length
    );
         uint256[] memory alltimes =new uint256[](
        users[referrerAddress].x6Matrix[level].firstLevelReferrals.length +
        users[referrerAddress].x6Matrix[level].secondLevelReferrals.length
    );
    
    uint256 participantIndex = 0;
     for (uint256 i = 0; i < users[referrerAddress].x6Matrix[level].firstLevelReferrals.length; i++) {
        allParticipants[participantIndex] = users[referrerAddress].x6Matrix[level].firstLevelReferrals[i];
        alltimes[participantIndex] = users[referrerAddress].x6Matrix[level].firstentrytime[i];
        participantIndex++;
    }
    
    // Add second-level referrals
    for (uint256 i = 0; i < users[referrerAddress].x6Matrix[level].secondLevelReferrals.length; i++) {
        allParticipants[participantIndex] = users[referrerAddress].x6Matrix[level].secondLevelReferrals[i];
        alltimes[participantIndex] = users[referrerAddress].x6Matrix[level].secondentrytime[i];
        participantIndex++;
    }
    
    users[referrerAddress].x6Matrix[level].cycles.push(CycleInfo({
        completionTime: alltimes,
        participants: allParticipants
    }));
    
    emit X6CycleCompleted(referrerAddress, level, cycleIndex);

        users[referrerAddress].x6Matrix[level].firstLevelReferrals = new address[](0);
        users[referrerAddress].x6Matrix[level].secondLevelReferrals = new address[](0);
        users[referrerAddress].x6Matrix[level].firstentrytime = new uint256[](0);
        users[referrerAddress].x6Matrix[level].secondentrytime = new uint256[](0);
        users[referrerAddress].x6Matrix[level].closedPart = address(0);

        if (!users[referrerAddress].activeX6Levels[level+1] && level != LAST_LEVEL) {
            users[referrerAddress].x6Matrix[level].blocked = true;
        }

        users[referrerAddress].x6Matrix[level].reinvestCount++;
        
        if (referrerAddress != id1) {
            address freeReferrerAddress = findFreeX6Referrer(referrerAddress, level);

            emit Reinvest(referrerAddress, freeReferrerAddress, userAddress, 2, level);
            updateX6Referrer(referrerAddress, freeReferrerAddress, level);
        } else {
            emit Reinvest(id1, address(0), userAddress, 2, level);
            sendETHDividends(id1, userAddress, 2, level);
        }
    }
    
    function findFreeX3Referrer(address userAddress, uint8 level) public view returns(address) {
        while (true) {
            if (users[users[userAddress].referrer].activeX3Levels[level]) {
                return users[userAddress].referrer;
            }
            
            userAddress = users[userAddress].referrer;
        }
    }
    
    function findFreeX6Referrer(address userAddress, uint8 level) public view returns(address) {
        while (true) {
            if (users[users[userAddress].referrer].activeX6Levels[level]) {
                return users[userAddress].referrer;
            }
            
            userAddress = users[userAddress].referrer;
        }
    }
        
    function usersActiveX3Levels(address userAddress, uint8 level) public view returns(bool) {
        return users[userAddress].activeX3Levels[level];
    }

    function usersActiveX6Levels(address userAddress, uint8 level) public view returns(bool) {
        return users[userAddress].activeX6Levels[level];
    }

    function usersX3Matrix(address userAddress, uint8 level) public view returns(address, address[] memory, bool) {
        return (users[userAddress].x3Matrix[level].currentReferrer,
                users[userAddress].x3Matrix[level].referrals,
                users[userAddress].x3Matrix[level].blocked);
    }

    function usersX6Matrix(address userAddress, uint8 level) public view returns(address, address[] memory, address[] memory, bool, address) {
        return (users[userAddress].x6Matrix[level].currentReferrer,
                users[userAddress].x6Matrix[level].firstLevelReferrals,
                users[userAddress].x6Matrix[level].secondLevelReferrals,
                users[userAddress].x6Matrix[level].blocked,
                users[userAddress].x6Matrix[level].closedPart);
    }

  function getRecentActivity() public view returns (RecentActivity[] memory) {
    // Create a dynamic array to store recent activities
    uint256 count = 0;
    uint256 oneHourAgo = block.timestamp - 1 hours;

    // First, count how many activities are within the last hour
    for (uint i = recentActivities.length; i > 0; i--) {
        RecentActivity memory activity = recentActivities[i - 1];
        if (activity.timestamp < oneHourAgo) break;
        count++;
    }

    // Create a memory array with the exact size needed
    RecentActivity[] memory recentActivityList = new RecentActivity[](count);
    
    // Reset count to use as an index while populating the array
    count = 0;
    
    // Populate the array with recent activities
    for (uint i = recentActivities.length; i > 0; i--) {
        RecentActivity memory activity = recentActivities[i - 1];
        if (activity.timestamp < oneHourAgo) break;
        
        recentActivityList[count] = activity;
        count++;
    }

    return recentActivityList;
}
    
    
    //
      function getTotalCycles(address userAddress, uint8 matrix, uint8 level) public view returns (uint256) {
        require(matrix == 1 || matrix == 2, "Invalid matrix");
        require(level > 0 && level <= LAST_LEVEL, "Invalid level");
        
        if (matrix == 1) {
            return users[userAddress].x3Matrix[level].cycles.length;
        } else {
            return users[userAddress].x6Matrix[level].cycles.length;
        }
    }

    //
   function getCycleInfo(address userAddress, uint8 matrix, uint8 level, uint256 cycleIndex) public view returns (uint256, address[] memory, uint256[] memory) {
        require(matrix == 1 || matrix == 2, "Invalid matrix");
        require(level > 0 && level <= LAST_LEVEL, "Invalid level");
        
        CycleInfo memory cycle;
        if (matrix == 1) {
            require(cycleIndex < users[userAddress].x3Matrix[level].cycles.length, "Invalid cycle index");
            cycle = users[userAddress].x3Matrix[level].cycles[cycleIndex];
        } else {
            require(cycleIndex < users[userAddress].x6Matrix[level].cycles.length, "Invalid cycle index");
            cycle = users[userAddress].x6Matrix[level].cycles[cycleIndex];
        }
        
        uint256[] memory registrationTimes = new uint256[](cycle.participants.length);
        for (uint256 i = 0; i < cycle.participants.length; i++) {
            registrationTimes[i] = users[cycle.participants[i]].registrationTime;
        }
        
        return (cycle.completionTime[cycle.completionTime.length-1], cycle.participants, registrationTimes);
    }

    
    function isUserExists(address user) public view returns (bool) {
        return (users[user].id != 0);
    }

    function findEthReceiver(address userAddress, address _from, uint8 matrix, uint8 level) private returns(address, bool) {
        address receiver = userAddress;
        bool isExtraDividends;
        if (matrix == 1) {
            while (true) {
                if (users[receiver].x3Matrix[level].blocked) {
                    emit MissedEthReceive(receiver, _from, 1, level);
                    isExtraDividends = true;
                    receiver = users[receiver].x3Matrix[level].currentReferrer;
                } else {
                    return (receiver, isExtraDividends);
                }
            }
        } else {
            while (true) {
                if (users[receiver].x6Matrix[level].blocked) {
                    emit MissedEthReceive(receiver, _from, 2, level);
                    isExtraDividends = true;
                    receiver = users[receiver].x6Matrix[level].currentReferrer;
                } else {
                    return (receiver, isExtraDividends);
                }
            }
        }
    }

    function sendETHDividends(address userAddress, address _from, uint8 matrix, uint8 level) private {
        (address receiver, bool isExtraDividends) = findEthReceiver(userAddress, _from, matrix, level);

        depositToken.safeTransfer(receiver, levelPrice[level]);
        // if (!address(uint160(receiver)).send(levelPrice[level])) {
        //     return address(uint160(receiver)).transfer(address(this).balance);
        // }
        
        if (isExtraDividends) {
            emit SentExtraEthDividends(_from, receiver, matrix, level);
        }
    }
    
    function bytesToAddress(bytes memory bys) private pure returns (address addr) {
        assembly {
            addr := mload(add(bys, 20))
        }
    }

    function withdrawLostTokens(address tokenAddress) public  onlyContractOwner {
        require(tokenAddress != address(depositToken), "cannot withdraw deposit token");
        if (tokenAddress == address(0)) {
            address(uint160(multisig)).transfer(address(this).balance);
        } else {
            IERC20(tokenAddress).transfer(multisig, IERC20(tokenAddress).balanceOf(address(this)));
        }
    }
    // Add this function to the SmartMatrixForsage contract

function getTeamSize(address userAddress) public view returns (uint256) {
    return _calculateTeamSize(userAddress, 0);
}

function _calculateTeamSize(address userAddress, uint256 depth) private view returns (uint256) {

    uint256 teamSize = users[userAddress].partnersCount;

    address[] memory partners = _getPartners(userAddress);
    for (uint256 i = 0; i < partners.length; i++) {
        teamSize += _calculateTeamSize(partners[i], depth + 1);
    }

    return teamSize;
}

function _getPartners(address userAddress) private view returns (address[] memory) {
    uint256 partnerCount = users[userAddress].partnersCount;
    address[] memory partners = new address[](partnerCount);
    uint256 count = 0;

    for (uint256 i = 1; i < lastUserId; i++) {
        if (users[userIds[i]].referrer == userAddress) {
            partners[count] = userIds[i];
            count++;
            if (count == partnerCount) {
                break;
            }
        }
    }


    return partners;
}
function getPartnerCount(address userAddress, uint8 matrix, uint8 level) public view returns (uint256) {
    require(isUserExists(userAddress), "User does not exist");
    require(matrix == 1 || matrix == 2, "Invalid matrix");
   
    require(level > 0 && level <= LAST_LEVEL, "Invalid level");

    uint256 directPartnerCount = 0;

    for (uint256 i = 1; i < lastUserId; i++) {
        address partnerAddress = userIds[i];
        if (allDirectPartners[userAddress][matrix][level][partnerAddress]) {
            directPartnerCount++;
        }
    }

    return directPartnerCount;
}

    function getDetailedMatrixInfo(
        uint256 userId, 
        uint8 matrix, 
        uint8 level
    ) public view returns (UserMatrixDetails[] memory) {
        require(matrix == 1 || matrix == 2, "Invalid matrix");
        require(level > 0 && level <= LAST_LEVEL, "Invalid level");
        require(userId > 0 && userId < lastUserId, "Invalid user ID");
        
        address userAddress = userIds[userId];
        require(userAddress != address(0), "User does not exist");
        
        uint256 totalUsers = 0;
        
        if (matrix == 1) {
            totalUsers = users[userAddress].x3Matrix[level].referrals.length + 
                        (users[userAddress].x3Matrix[level].cycles.length * 3);
        } else {
            totalUsers = users[userAddress].x6Matrix[level].firstLevelReferrals.length +
                        users[userAddress].x6Matrix[level].secondLevelReferrals.length +
                        (users[userAddress].x6Matrix[level].cycles.length * 6);
        }
        
        UserMatrixDetails[] memory details = new UserMatrixDetails[](totalUsers);
        uint256 currentIndex = 0;
        
        if (matrix == 1) {
            // Current X3 matrix users
            for (uint256 i = 0; i < users[userAddress].x3Matrix[level].referrals.length; i++) {
                address participant = users[userAddress].x3Matrix[level].referrals[i];
                uint256 tym = users[userAddress].x3Matrix[level].entrytime[i];
                details[currentIndex] = UserMatrixDetails({
                    userId: users[participant].id,
                    userAddress: participant,
                    timestamp: tym,
                    matrix: matrix,
                    level: level,
                    userType: "Normal",
                    cycleNumber: 0,
                    tokenAmount: levelPrice[level]
                });
                currentIndex++;
            }
            
            // Completed X3 cycles
            for (uint256 c = 0; c < users[userAddress].x3Matrix[level].cycles.length; c++) {
                CycleInfo memory cycle = users[userAddress].x3Matrix[level].cycles[c];
                for (uint256 i = 0; i < cycle.participants.length; i++) {
                    address participant = cycle.participants[i];
                    uint256 tym = cycle.completionTime[i];
                    details[currentIndex] = UserMatrixDetails({
                        userId: users[participant].id,
                        userAddress: participant,
                        timestamp: tym,
                        matrix: matrix,
                        level: level,
                        userType: i == 2 ? "Recycled" : "Normal",
                        cycleNumber: c + 1,
                        tokenAmount: levelPrice[level]
                    });
                    currentIndex++;
                }
            }
        } else {
            // Current X6 first level referrals
            for (uint256 i = 0; i < users[userAddress].x6Matrix[level].firstLevelReferrals.length; i++) {
                address participant = users[userAddress].x6Matrix[level].firstLevelReferrals[i];
                uint256 tym = users[userAddress].x6Matrix[level].firstentrytime[i];
                details[currentIndex] = UserMatrixDetails({
                    userId: users[participant].id,
                    userAddress: participant,
                    timestamp: tym,
                    matrix: matrix,
                    level: level,
                    userType: "Normal",
                    cycleNumber: 0,
                    tokenAmount: levelPrice[level]
                });
                currentIndex++;
            }
            
            // Current X6 second level referrals
            for (uint256 i = 0; i < users[userAddress].x6Matrix[level].secondLevelReferrals.length; i++) {
                address participant = users[userAddress].x6Matrix[level].secondLevelReferrals[i];
                uint256 tym = users[userAddress].x6Matrix[level].secondentrytime[i];
                details[currentIndex] = UserMatrixDetails({
                    userId: users[participant].id,
                    userAddress: participant,
                    timestamp: tym,
                    matrix: matrix,
                    level: level,
                    userType: "Normal",
                    cycleNumber: 0,
                    tokenAmount: levelPrice[level]
                });
                currentIndex++;
            }
            
            // Completed X6 cycles
            for (uint256 c = 0; c < users[userAddress].x6Matrix[level].cycles.length; c++) {
                CycleInfo memory cycle = users[userAddress].x6Matrix[level].cycles[c];
                for (uint256 i = 0; i < cycle.participants.length; i++) {
                    address participant = cycle.participants[i];
                    uint256 tym = cycle.completionTime[i];
                    details[currentIndex] = UserMatrixDetails({
                        userId: users[participant].id,
                        userAddress: participant,
                        timestamp: tym,
                        matrix: matrix,
                        level: level,
                        userType: i == cycle.participants.length - 1 ? "Recycled" : "Normal",
                        cycleNumber: c + 1,
                        tokenAmount: levelPrice[level]
                    });
                    currentIndex++;
                }
            }
        }
        return details;
    }
   
}
