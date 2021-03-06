'use strict';

Object.defineProperty(exports, '__esModule', { value: true });

function _interopDefault (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var Taro = _interopDefault(require('@tarojs/taro-h5'));
var Nerv = require('nervjs');
var Nerv__default = _interopDefault(Nerv);

function _typeof(obj) {
  "@babel/helpers - typeof";

  if (typeof Symbol === "function" && typeof Symbol.iterator === "symbol") {
    _typeof = function (obj) {
      return typeof obj;
    };
  } else {
    _typeof = function (obj) {
      return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
    };
  }

  return _typeof(obj);
}

function _classCallCheck(instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
}

function _defineProperties(target, props) {
  for (var i = 0; i < props.length; i++) {
    var descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ("value" in descriptor) descriptor.writable = true;
    Object.defineProperty(target, descriptor.key, descriptor);
  }
}

function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  return Constructor;
}

function _inherits(subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function");
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      writable: true,
      configurable: true
    }
  });
  if (superClass) _setPrototypeOf(subClass, superClass);
}

function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf : function _getPrototypeOf(o) {
    return o.__proto__ || Object.getPrototypeOf(o);
  };
  return _getPrototypeOf(o);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf || function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };

  return _setPrototypeOf(o, p);
}

function _isNativeReflectConstruct() {
  if (typeof Reflect === "undefined" || !Reflect.construct) return false;
  if (Reflect.construct.sham) return false;
  if (typeof Proxy === "function") return true;

  try {
    Date.prototype.toString.call(Reflect.construct(Date, [], function () {}));
    return true;
  } catch (e) {
    return false;
  }
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function _possibleConstructorReturn(self, call) {
  if (call && (typeof call === "object" || typeof call === "function")) {
    return call;
  }

  return _assertThisInitialized(self);
}

function _createSuper(Derived) {
  var hasNativeReflectConstruct = _isNativeReflectConstruct();

  return function () {
    var Super = _getPrototypeOf(Derived),
        result;

    if (hasNativeReflectConstruct) {
      var NewTarget = _getPrototypeOf(this).constructor;

      result = Reflect.construct(Super, arguments, NewTarget);
    } else {
      result = Super.apply(this, arguments);
    }

    return _possibleConstructorReturn(this, result);
  };
}

function _superPropBase(object, property) {
  while (!Object.prototype.hasOwnProperty.call(object, property)) {
    object = _getPrototypeOf(object);
    if (object === null) break;
  }

  return object;
}

function _get(target, property, receiver) {
  if (typeof Reflect !== "undefined" && Reflect.get) {
    _get = Reflect.get;
  } else {
    _get = function _get(target, property, receiver) {
      var base = _superPropBase(target, property);

      if (!base) return;
      var desc = Object.getOwnPropertyDescriptor(base, property);

      if (desc.get) {
        return desc.get.call(receiver);
      }

      return desc.value;
    };
  }

  return _get(target, property, receiver || target);
}

function _slicedToArray(arr, i) {
  return _arrayWithHoles(arr) || _iterableToArrayLimit(arr, i) || _unsupportedIterableToArray(arr, i) || _nonIterableRest();
}

function _toConsumableArray(arr) {
  return _arrayWithoutHoles(arr) || _iterableToArray(arr) || _unsupportedIterableToArray(arr) || _nonIterableSpread();
}

function _arrayWithoutHoles(arr) {
  if (Array.isArray(arr)) return _arrayLikeToArray(arr);
}

function _arrayWithHoles(arr) {
  if (Array.isArray(arr)) return arr;
}

function _iterableToArray(iter) {
  if (typeof Symbol !== "undefined" && Symbol.iterator in Object(iter)) return Array.from(iter);
}

function _iterableToArrayLimit(arr, i) {
  if (typeof Symbol === "undefined" || !(Symbol.iterator in Object(arr))) return;
  var _arr = [];
  var _n = true;
  var _d = false;
  var _e = undefined;

  try {
    for (var _i = arr[Symbol.iterator](), _s; !(_n = (_s = _i.next()).done); _n = true) {
      _arr.push(_s.value);

      if (i && _arr.length === i) break;
    }
  } catch (err) {
    _d = true;
    _e = err;
  } finally {
    try {
      if (!_n && _i["return"] != null) _i["return"]();
    } finally {
      if (_d) throw _e;
    }
  }

  return _arr;
}

function _unsupportedIterableToArray(o, minLen) {
  if (!o) return;
  if (typeof o === "string") return _arrayLikeToArray(o, minLen);
  var n = Object.prototype.toString.call(o).slice(8, -1);
  if (n === "Object" && o.constructor) n = o.constructor.name;
  if (n === "Map" || n === "Set") return Array.from(o);
  if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen);
}

function _arrayLikeToArray(arr, len) {
  if (len == null || len > arr.length) len = arr.length;

  for (var i = 0, arr2 = new Array(len); i < len; i++) arr2[i] = arr[i];

  return arr2;
}

function _nonIterableSpread() {
  throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.");
}

function _nonIterableRest() {
  throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.");
}

/**
 * Copyright (c) 2014-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/**
 * Similar to invariant but only logs a warning if the condition is not met.
 * This can be used to log issues in development environments in critical
 * paths. Removing the logging code for production environments will keep the
 * same logic and follow the same code paths.
 */

var __DEV__ = process.env.NODE_ENV !== 'production';

var warning = function() {};

if (__DEV__) {
  var printWarning = function printWarning(format, args) {
    var len = arguments.length;
    args = new Array(len > 2 ? len - 2 : 0);
    for (var key = 2; key < len; key++) {
      args[key - 2] = arguments[key];
    }
    var argIndex = 0;
    var message = 'Warning: ' +
      format.replace(/%s/g, function() {
        return args[argIndex++];
      });
    if (typeof console !== 'undefined') {
      console.error(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };

  warning = function(condition, format, args) {
    var len = arguments.length;
    args = new Array(len > 2 ? len - 2 : 0);
    for (var key = 2; key < len; key++) {
      args[key - 2] = arguments[key];
    }
    if (format === undefined) {
      throw new Error(
          '`warning(condition, format, ...args)` requires a warning ' +
          'message argument'
      );
    }
    if (!condition) {
      printWarning.apply(null, [format].concat(args));
    }
  };
}

var warning_1 = warning;

var commonjsGlobal = typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function createCommonjsModule(fn, module) {
	return module = { exports: {} }, fn(module, module.exports), module.exports;
}

/** Detect free variable `global` from Node.js. */
var freeGlobal = typeof commonjsGlobal == 'object' && commonjsGlobal && commonjsGlobal.Object === Object && commonjsGlobal;

var _freeGlobal = freeGlobal;

/** Detect free variable `self`. */
var freeSelf = typeof self == 'object' && self && self.Object === Object && self;

/** Used as a reference to the global object. */
var root = _freeGlobal || freeSelf || Function('return this')();

var _root = root;

/** Built-in value references. */
var Symbol$1 = _root.Symbol;

var _Symbol = Symbol$1;

/** Used for built-in method references. */
var objectProto = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty = objectProto.hasOwnProperty;

/**
 * Used to resolve the
 * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
 * of values.
 */
var nativeObjectToString = objectProto.toString;

/** Built-in value references. */
var symToStringTag = _Symbol ? _Symbol.toStringTag : undefined;

/**
 * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
 *
 * @private
 * @param {*} value The value to query.
 * @returns {string} Returns the raw `toStringTag`.
 */
function getRawTag(value) {
  var isOwn = hasOwnProperty.call(value, symToStringTag),
      tag = value[symToStringTag];

  try {
    value[symToStringTag] = undefined;
    var unmasked = true;
  } catch (e) {}

  var result = nativeObjectToString.call(value);
  if (unmasked) {
    if (isOwn) {
      value[symToStringTag] = tag;
    } else {
      delete value[symToStringTag];
    }
  }
  return result;
}

var _getRawTag = getRawTag;

/** Used for built-in method references. */
var objectProto$1 = Object.prototype;

/**
 * Used to resolve the
 * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
 * of values.
 */
var nativeObjectToString$1 = objectProto$1.toString;

/**
 * Converts `value` to a string using `Object.prototype.toString`.
 *
 * @private
 * @param {*} value The value to convert.
 * @returns {string} Returns the converted string.
 */
function objectToString(value) {
  return nativeObjectToString$1.call(value);
}

var _objectToString = objectToString;

/** `Object#toString` result references. */
var nullTag = '[object Null]',
    undefinedTag = '[object Undefined]';

/** Built-in value references. */
var symToStringTag$1 = _Symbol ? _Symbol.toStringTag : undefined;

/**
 * The base implementation of `getTag` without fallbacks for buggy environments.
 *
 * @private
 * @param {*} value The value to query.
 * @returns {string} Returns the `toStringTag`.
 */
function baseGetTag(value) {
  if (value == null) {
    return value === undefined ? undefinedTag : nullTag;
  }
  return (symToStringTag$1 && symToStringTag$1 in Object(value))
    ? _getRawTag(value)
    : _objectToString(value);
}

var _baseGetTag = baseGetTag;

/**
 * Checks if `value` is the
 * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
 * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
 *
 * @static
 * @memberOf _
 * @since 0.1.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is an object, else `false`.
 * @example
 *
 * _.isObject({});
 * // => true
 *
 * _.isObject([1, 2, 3]);
 * // => true
 *
 * _.isObject(_.noop);
 * // => true
 *
 * _.isObject(null);
 * // => false
 */
function isObject(value) {
  var type = typeof value;
  return value != null && (type == 'object' || type == 'function');
}

var isObject_1 = isObject;

/** `Object#toString` result references. */
var asyncTag = '[object AsyncFunction]',
    funcTag = '[object Function]',
    genTag = '[object GeneratorFunction]',
    proxyTag = '[object Proxy]';

/**
 * Checks if `value` is classified as a `Function` object.
 *
 * @static
 * @memberOf _
 * @since 0.1.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a function, else `false`.
 * @example
 *
 * _.isFunction(_);
 * // => true
 *
 * _.isFunction(/abc/);
 * // => false
 */
function isFunction(value) {
  if (!isObject_1(value)) {
    return false;
  }
  // The use of `Object#toString` avoids issues with the `typeof` operator
  // in Safari 9 which returns 'object' for typed arrays and other constructors.
  var tag = _baseGetTag(value);
  return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag;
}

var isFunction_1 = isFunction;

/** Used to detect overreaching core-js shims. */
var coreJsData = _root['__core-js_shared__'];

var _coreJsData = coreJsData;

/** Used to detect methods masquerading as native. */
var maskSrcKey = (function() {
  var uid = /[^.]+$/.exec(_coreJsData && _coreJsData.keys && _coreJsData.keys.IE_PROTO || '');
  return uid ? ('Symbol(src)_1.' + uid) : '';
}());

/**
 * Checks if `func` has its source masked.
 *
 * @private
 * @param {Function} func The function to check.
 * @returns {boolean} Returns `true` if `func` is masked, else `false`.
 */
function isMasked(func) {
  return !!maskSrcKey && (maskSrcKey in func);
}

var _isMasked = isMasked;

/** Used for built-in method references. */
var funcProto = Function.prototype;

/** Used to resolve the decompiled source of functions. */
var funcToString = funcProto.toString;

/**
 * Converts `func` to its source code.
 *
 * @private
 * @param {Function} func The function to convert.
 * @returns {string} Returns the source code.
 */
function toSource(func) {
  if (func != null) {
    try {
      return funcToString.call(func);
    } catch (e) {}
    try {
      return (func + '');
    } catch (e) {}
  }
  return '';
}

var _toSource = toSource;

/**
 * Used to match `RegExp`
 * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
 */
var reRegExpChar = /[\\^$.*+?()[\]{}|]/g;

/** Used to detect host constructors (Safari). */
var reIsHostCtor = /^\[object .+?Constructor\]$/;

/** Used for built-in method references. */
var funcProto$1 = Function.prototype,
    objectProto$2 = Object.prototype;

/** Used to resolve the decompiled source of functions. */
var funcToString$1 = funcProto$1.toString;

/** Used to check objects for own properties. */
var hasOwnProperty$1 = objectProto$2.hasOwnProperty;

/** Used to detect if a method is native. */
var reIsNative = RegExp('^' +
  funcToString$1.call(hasOwnProperty$1).replace(reRegExpChar, '\\$&')
  .replace(/hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g, '$1.*?') + '$'
);

/**
 * The base implementation of `_.isNative` without bad shim checks.
 *
 * @private
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a native function,
 *  else `false`.
 */
function baseIsNative(value) {
  if (!isObject_1(value) || _isMasked(value)) {
    return false;
  }
  var pattern = isFunction_1(value) ? reIsNative : reIsHostCtor;
  return pattern.test(_toSource(value));
}

var _baseIsNative = baseIsNative;

/**
 * Gets the value at `key` of `object`.
 *
 * @private
 * @param {Object} [object] The object to query.
 * @param {string} key The key of the property to get.
 * @returns {*} Returns the property value.
 */
function getValue(object, key) {
  return object == null ? undefined : object[key];
}

var _getValue = getValue;

/**
 * Gets the native function at `key` of `object`.
 *
 * @private
 * @param {Object} object The object to query.
 * @param {string} key The key of the method to get.
 * @returns {*} Returns the function if it's native, else `undefined`.
 */
function getNative(object, key) {
  var value = _getValue(object, key);
  return _baseIsNative(value) ? value : undefined;
}

var _getNative = getNative;

var defineProperty = (function() {
  try {
    var func = _getNative(Object, 'defineProperty');
    func({}, '', {});
    return func;
  } catch (e) {}
}());

var _defineProperty$1 = defineProperty;

/**
 * The base implementation of `assignValue` and `assignMergeValue` without
 * value checks.
 *
 * @private
 * @param {Object} object The object to modify.
 * @param {string} key The key of the property to assign.
 * @param {*} value The value to assign.
 */
function baseAssignValue(object, key, value) {
  if (key == '__proto__' && _defineProperty$1) {
    _defineProperty$1(object, key, {
      'configurable': true,
      'enumerable': true,
      'value': value,
      'writable': true
    });
  } else {
    object[key] = value;
  }
}

var _baseAssignValue = baseAssignValue;

/**
 * Performs a
 * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
 * comparison between two values to determine if they are equivalent.
 *
 * @static
 * @memberOf _
 * @since 4.0.0
 * @category Lang
 * @param {*} value The value to compare.
 * @param {*} other The other value to compare.
 * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
 * @example
 *
 * var object = { 'a': 1 };
 * var other = { 'a': 1 };
 *
 * _.eq(object, object);
 * // => true
 *
 * _.eq(object, other);
 * // => false
 *
 * _.eq('a', 'a');
 * // => true
 *
 * _.eq('a', Object('a'));
 * // => false
 *
 * _.eq(NaN, NaN);
 * // => true
 */
function eq(value, other) {
  return value === other || (value !== value && other !== other);
}

var eq_1 = eq;

/** Used for built-in method references. */
var objectProto$3 = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty$2 = objectProto$3.hasOwnProperty;

/**
 * Assigns `value` to `key` of `object` if the existing value is not equivalent
 * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
 * for equality comparisons.
 *
 * @private
 * @param {Object} object The object to modify.
 * @param {string} key The key of the property to assign.
 * @param {*} value The value to assign.
 */
function assignValue(object, key, value) {
  var objValue = object[key];
  if (!(hasOwnProperty$2.call(object, key) && eq_1(objValue, value)) ||
      (value === undefined && !(key in object))) {
    _baseAssignValue(object, key, value);
  }
}

var _assignValue = assignValue;

/**
 * Copies properties of `source` to `object`.
 *
 * @private
 * @param {Object} source The object to copy properties from.
 * @param {Array} props The property identifiers to copy.
 * @param {Object} [object={}] The object to copy properties to.
 * @param {Function} [customizer] The function to customize copied values.
 * @returns {Object} Returns `object`.
 */
function copyObject(source, props, object, customizer) {
  var isNew = !object;
  object || (object = {});

  var index = -1,
      length = props.length;

  while (++index < length) {
    var key = props[index];

    var newValue = customizer
      ? customizer(object[key], source[key], key, object, source)
      : undefined;

    if (newValue === undefined) {
      newValue = source[key];
    }
    if (isNew) {
      _baseAssignValue(object, key, newValue);
    } else {
      _assignValue(object, key, newValue);
    }
  }
  return object;
}

var _copyObject = copyObject;

/**
 * This method returns the first argument it receives.
 *
 * @static
 * @since 0.1.0
 * @memberOf _
 * @category Util
 * @param {*} value Any value.
 * @returns {*} Returns `value`.
 * @example
 *
 * var object = { 'a': 1 };
 *
 * console.log(_.identity(object) === object);
 * // => true
 */
function identity(value) {
  return value;
}

var identity_1 = identity;

/**
 * A faster alternative to `Function#apply`, this function invokes `func`
 * with the `this` binding of `thisArg` and the arguments of `args`.
 *
 * @private
 * @param {Function} func The function to invoke.
 * @param {*} thisArg The `this` binding of `func`.
 * @param {Array} args The arguments to invoke `func` with.
 * @returns {*} Returns the result of `func`.
 */
function apply(func, thisArg, args) {
  switch (args.length) {
    case 0: return func.call(thisArg);
    case 1: return func.call(thisArg, args[0]);
    case 2: return func.call(thisArg, args[0], args[1]);
    case 3: return func.call(thisArg, args[0], args[1], args[2]);
  }
  return func.apply(thisArg, args);
}

var _apply = apply;

/* Built-in method references for those with the same name as other `lodash` methods. */
var nativeMax = Math.max;

/**
 * A specialized version of `baseRest` which transforms the rest array.
 *
 * @private
 * @param {Function} func The function to apply a rest parameter to.
 * @param {number} [start=func.length-1] The start position of the rest parameter.
 * @param {Function} transform The rest array transform.
 * @returns {Function} Returns the new function.
 */
function overRest(func, start, transform) {
  start = nativeMax(start === undefined ? (func.length - 1) : start, 0);
  return function() {
    var args = arguments,
        index = -1,
        length = nativeMax(args.length - start, 0),
        array = Array(length);

    while (++index < length) {
      array[index] = args[start + index];
    }
    index = -1;
    var otherArgs = Array(start + 1);
    while (++index < start) {
      otherArgs[index] = args[index];
    }
    otherArgs[start] = transform(array);
    return _apply(func, this, otherArgs);
  };
}

var _overRest = overRest;

/**
 * Creates a function that returns `value`.
 *
 * @static
 * @memberOf _
 * @since 2.4.0
 * @category Util
 * @param {*} value The value to return from the new function.
 * @returns {Function} Returns the new constant function.
 * @example
 *
 * var objects = _.times(2, _.constant({ 'a': 1 }));
 *
 * console.log(objects);
 * // => [{ 'a': 1 }, { 'a': 1 }]
 *
 * console.log(objects[0] === objects[1]);
 * // => true
 */
function constant(value) {
  return function() {
    return value;
  };
}

var constant_1 = constant;

/**
 * The base implementation of `setToString` without support for hot loop shorting.
 *
 * @private
 * @param {Function} func The function to modify.
 * @param {Function} string The `toString` result.
 * @returns {Function} Returns `func`.
 */
var baseSetToString = !_defineProperty$1 ? identity_1 : function(func, string) {
  return _defineProperty$1(func, 'toString', {
    'configurable': true,
    'enumerable': false,
    'value': constant_1(string),
    'writable': true
  });
};

var _baseSetToString = baseSetToString;

/** Used to detect hot functions by number of calls within a span of milliseconds. */
var HOT_COUNT = 800,
    HOT_SPAN = 16;

/* Built-in method references for those with the same name as other `lodash` methods. */
var nativeNow = Date.now;

/**
 * Creates a function that'll short out and invoke `identity` instead
 * of `func` when it's called `HOT_COUNT` or more times in `HOT_SPAN`
 * milliseconds.
 *
 * @private
 * @param {Function} func The function to restrict.
 * @returns {Function} Returns the new shortable function.
 */
function shortOut(func) {
  var count = 0,
      lastCalled = 0;

  return function() {
    var stamp = nativeNow(),
        remaining = HOT_SPAN - (stamp - lastCalled);

    lastCalled = stamp;
    if (remaining > 0) {
      if (++count >= HOT_COUNT) {
        return arguments[0];
      }
    } else {
      count = 0;
    }
    return func.apply(undefined, arguments);
  };
}

var _shortOut = shortOut;

/**
 * Sets the `toString` method of `func` to return `string`.
 *
 * @private
 * @param {Function} func The function to modify.
 * @param {Function} string The `toString` result.
 * @returns {Function} Returns `func`.
 */
var setToString = _shortOut(_baseSetToString);

var _setToString = setToString;

/**
 * The base implementation of `_.rest` which doesn't validate or coerce arguments.
 *
 * @private
 * @param {Function} func The function to apply a rest parameter to.
 * @param {number} [start=func.length-1] The start position of the rest parameter.
 * @returns {Function} Returns the new function.
 */
function baseRest(func, start) {
  return _setToString(_overRest(func, start, identity_1), func + '');
}

var _baseRest = baseRest;

/** Used as references for various `Number` constants. */
var MAX_SAFE_INTEGER = 9007199254740991;

/**
 * Checks if `value` is a valid array-like length.
 *
 * **Note:** This method is loosely based on
 * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
 *
 * @static
 * @memberOf _
 * @since 4.0.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a valid length, else `false`.
 * @example
 *
 * _.isLength(3);
 * // => true
 *
 * _.isLength(Number.MIN_VALUE);
 * // => false
 *
 * _.isLength(Infinity);
 * // => false
 *
 * _.isLength('3');
 * // => false
 */
function isLength(value) {
  return typeof value == 'number' &&
    value > -1 && value % 1 == 0 && value <= MAX_SAFE_INTEGER;
}

var isLength_1 = isLength;

/**
 * Checks if `value` is array-like. A value is considered array-like if it's
 * not a function and has a `value.length` that's an integer greater than or
 * equal to `0` and less than or equal to `Number.MAX_SAFE_INTEGER`.
 *
 * @static
 * @memberOf _
 * @since 4.0.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is array-like, else `false`.
 * @example
 *
 * _.isArrayLike([1, 2, 3]);
 * // => true
 *
 * _.isArrayLike(document.body.children);
 * // => true
 *
 * _.isArrayLike('abc');
 * // => true
 *
 * _.isArrayLike(_.noop);
 * // => false
 */
function isArrayLike(value) {
  return value != null && isLength_1(value.length) && !isFunction_1(value);
}

var isArrayLike_1 = isArrayLike;

/** Used as references for various `Number` constants. */
var MAX_SAFE_INTEGER$1 = 9007199254740991;

/** Used to detect unsigned integer values. */
var reIsUint = /^(?:0|[1-9]\d*)$/;

/**
 * Checks if `value` is a valid array-like index.
 *
 * @private
 * @param {*} value The value to check.
 * @param {number} [length=MAX_SAFE_INTEGER] The upper bounds of a valid index.
 * @returns {boolean} Returns `true` if `value` is a valid index, else `false`.
 */
function isIndex(value, length) {
  var type = typeof value;
  length = length == null ? MAX_SAFE_INTEGER$1 : length;

  return !!length &&
    (type == 'number' ||
      (type != 'symbol' && reIsUint.test(value))) &&
        (value > -1 && value % 1 == 0 && value < length);
}

var _isIndex = isIndex;

/**
 * Checks if the given arguments are from an iteratee call.
 *
 * @private
 * @param {*} value The potential iteratee value argument.
 * @param {*} index The potential iteratee index or key argument.
 * @param {*} object The potential iteratee object argument.
 * @returns {boolean} Returns `true` if the arguments are from an iteratee call,
 *  else `false`.
 */
function isIterateeCall(value, index, object) {
  if (!isObject_1(object)) {
    return false;
  }
  var type = typeof index;
  if (type == 'number'
        ? (isArrayLike_1(object) && _isIndex(index, object.length))
        : (type == 'string' && index in object)
      ) {
    return eq_1(object[index], value);
  }
  return false;
}

var _isIterateeCall = isIterateeCall;

/**
 * Creates a function like `_.assign`.
 *
 * @private
 * @param {Function} assigner The function to assign values.
 * @returns {Function} Returns the new assigner function.
 */
function createAssigner(assigner) {
  return _baseRest(function(object, sources) {
    var index = -1,
        length = sources.length,
        customizer = length > 1 ? sources[length - 1] : undefined,
        guard = length > 2 ? sources[2] : undefined;

    customizer = (assigner.length > 3 && typeof customizer == 'function')
      ? (length--, customizer)
      : undefined;

    if (guard && _isIterateeCall(sources[0], sources[1], guard)) {
      customizer = length < 3 ? undefined : customizer;
      length = 1;
    }
    object = Object(object);
    while (++index < length) {
      var source = sources[index];
      if (source) {
        assigner(object, source, index, customizer);
      }
    }
    return object;
  });
}

var _createAssigner = createAssigner;

/** Used for built-in method references. */
var objectProto$4 = Object.prototype;

/**
 * Checks if `value` is likely a prototype object.
 *
 * @private
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a prototype, else `false`.
 */
function isPrototype(value) {
  var Ctor = value && value.constructor,
      proto = (typeof Ctor == 'function' && Ctor.prototype) || objectProto$4;

  return value === proto;
}

var _isPrototype = isPrototype;

/**
 * The base implementation of `_.times` without support for iteratee shorthands
 * or max array length checks.
 *
 * @private
 * @param {number} n The number of times to invoke `iteratee`.
 * @param {Function} iteratee The function invoked per iteration.
 * @returns {Array} Returns the array of results.
 */
function baseTimes(n, iteratee) {
  var index = -1,
      result = Array(n);

  while (++index < n) {
    result[index] = iteratee(index);
  }
  return result;
}

var _baseTimes = baseTimes;

/**
 * Checks if `value` is object-like. A value is object-like if it's not `null`
 * and has a `typeof` result of "object".
 *
 * @static
 * @memberOf _
 * @since 4.0.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
 * @example
 *
 * _.isObjectLike({});
 * // => true
 *
 * _.isObjectLike([1, 2, 3]);
 * // => true
 *
 * _.isObjectLike(_.noop);
 * // => false
 *
 * _.isObjectLike(null);
 * // => false
 */
function isObjectLike(value) {
  return value != null && typeof value == 'object';
}

var isObjectLike_1 = isObjectLike;

/** `Object#toString` result references. */
var argsTag = '[object Arguments]';

/**
 * The base implementation of `_.isArguments`.
 *
 * @private
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is an `arguments` object,
 */
function baseIsArguments(value) {
  return isObjectLike_1(value) && _baseGetTag(value) == argsTag;
}

var _baseIsArguments = baseIsArguments;

/** Used for built-in method references. */
var objectProto$5 = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty$3 = objectProto$5.hasOwnProperty;

/** Built-in value references. */
var propertyIsEnumerable = objectProto$5.propertyIsEnumerable;

/**
 * Checks if `value` is likely an `arguments` object.
 *
 * @static
 * @memberOf _
 * @since 0.1.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is an `arguments` object,
 *  else `false`.
 * @example
 *
 * _.isArguments(function() { return arguments; }());
 * // => true
 *
 * _.isArguments([1, 2, 3]);
 * // => false
 */
var isArguments = _baseIsArguments(function() { return arguments; }()) ? _baseIsArguments : function(value) {
  return isObjectLike_1(value) && hasOwnProperty$3.call(value, 'callee') &&
    !propertyIsEnumerable.call(value, 'callee');
};

var isArguments_1 = isArguments;

/**
 * Checks if `value` is classified as an `Array` object.
 *
 * @static
 * @memberOf _
 * @since 0.1.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is an array, else `false`.
 * @example
 *
 * _.isArray([1, 2, 3]);
 * // => true
 *
 * _.isArray(document.body.children);
 * // => false
 *
 * _.isArray('abc');
 * // => false
 *
 * _.isArray(_.noop);
 * // => false
 */
var isArray = Array.isArray;

var isArray_1 = isArray;

/**
 * This method returns `false`.
 *
 * @static
 * @memberOf _
 * @since 4.13.0
 * @category Util
 * @returns {boolean} Returns `false`.
 * @example
 *
 * _.times(2, _.stubFalse);
 * // => [false, false]
 */
function stubFalse() {
  return false;
}

var stubFalse_1 = stubFalse;

var isBuffer_1 = createCommonjsModule(function (module, exports) {
/** Detect free variable `exports`. */
var freeExports = exports && !exports.nodeType && exports;

/** Detect free variable `module`. */
var freeModule = freeExports && 'object' == 'object' && module && !module.nodeType && module;

/** Detect the popular CommonJS extension `module.exports`. */
var moduleExports = freeModule && freeModule.exports === freeExports;

/** Built-in value references. */
var Buffer = moduleExports ? _root.Buffer : undefined;

/* Built-in method references for those with the same name as other `lodash` methods. */
var nativeIsBuffer = Buffer ? Buffer.isBuffer : undefined;

/**
 * Checks if `value` is a buffer.
 *
 * @static
 * @memberOf _
 * @since 4.3.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a buffer, else `false`.
 * @example
 *
 * _.isBuffer(new Buffer(2));
 * // => true
 *
 * _.isBuffer(new Uint8Array(2));
 * // => false
 */
var isBuffer = nativeIsBuffer || stubFalse_1;

module.exports = isBuffer;
});

/** `Object#toString` result references. */
var argsTag$1 = '[object Arguments]',
    arrayTag = '[object Array]',
    boolTag = '[object Boolean]',
    dateTag = '[object Date]',
    errorTag = '[object Error]',
    funcTag$1 = '[object Function]',
    mapTag = '[object Map]',
    numberTag = '[object Number]',
    objectTag = '[object Object]',
    regexpTag = '[object RegExp]',
    setTag = '[object Set]',
    stringTag = '[object String]',
    weakMapTag = '[object WeakMap]';

var arrayBufferTag = '[object ArrayBuffer]',
    dataViewTag = '[object DataView]',
    float32Tag = '[object Float32Array]',
    float64Tag = '[object Float64Array]',
    int8Tag = '[object Int8Array]',
    int16Tag = '[object Int16Array]',
    int32Tag = '[object Int32Array]',
    uint8Tag = '[object Uint8Array]',
    uint8ClampedTag = '[object Uint8ClampedArray]',
    uint16Tag = '[object Uint16Array]',
    uint32Tag = '[object Uint32Array]';

/** Used to identify `toStringTag` values of typed arrays. */
var typedArrayTags = {};
typedArrayTags[float32Tag] = typedArrayTags[float64Tag] =
typedArrayTags[int8Tag] = typedArrayTags[int16Tag] =
typedArrayTags[int32Tag] = typedArrayTags[uint8Tag] =
typedArrayTags[uint8ClampedTag] = typedArrayTags[uint16Tag] =
typedArrayTags[uint32Tag] = true;
typedArrayTags[argsTag$1] = typedArrayTags[arrayTag] =
typedArrayTags[arrayBufferTag] = typedArrayTags[boolTag] =
typedArrayTags[dataViewTag] = typedArrayTags[dateTag] =
typedArrayTags[errorTag] = typedArrayTags[funcTag$1] =
typedArrayTags[mapTag] = typedArrayTags[numberTag] =
typedArrayTags[objectTag] = typedArrayTags[regexpTag] =
typedArrayTags[setTag] = typedArrayTags[stringTag] =
typedArrayTags[weakMapTag] = false;

/**
 * The base implementation of `_.isTypedArray` without Node.js optimizations.
 *
 * @private
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
 */
function baseIsTypedArray(value) {
  return isObjectLike_1(value) &&
    isLength_1(value.length) && !!typedArrayTags[_baseGetTag(value)];
}

var _baseIsTypedArray = baseIsTypedArray;

/**
 * The base implementation of `_.unary` without support for storing metadata.
 *
 * @private
 * @param {Function} func The function to cap arguments for.
 * @returns {Function} Returns the new capped function.
 */
function baseUnary(func) {
  return function(value) {
    return func(value);
  };
}

var _baseUnary = baseUnary;

var _nodeUtil = createCommonjsModule(function (module, exports) {
/** Detect free variable `exports`. */
var freeExports = exports && !exports.nodeType && exports;

/** Detect free variable `module`. */
var freeModule = freeExports && 'object' == 'object' && module && !module.nodeType && module;

/** Detect the popular CommonJS extension `module.exports`. */
var moduleExports = freeModule && freeModule.exports === freeExports;

/** Detect free variable `process` from Node.js. */
var freeProcess = moduleExports && _freeGlobal.process;

/** Used to access faster Node.js helpers. */
var nodeUtil = (function() {
  try {
    // Use `util.types` for Node.js 10+.
    var types = freeModule && freeModule.require && freeModule.require('util').types;

    if (types) {
      return types;
    }

    // Legacy `process.binding('util')` for Node.js < 10.
    return freeProcess && freeProcess.binding && freeProcess.binding('util');
  } catch (e) {}
}());

module.exports = nodeUtil;
});

/* Node.js helper references. */
var nodeIsTypedArray = _nodeUtil && _nodeUtil.isTypedArray;

/**
 * Checks if `value` is classified as a typed array.
 *
 * @static
 * @memberOf _
 * @since 3.0.0
 * @category Lang
 * @param {*} value The value to check.
 * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
 * @example
 *
 * _.isTypedArray(new Uint8Array);
 * // => true
 *
 * _.isTypedArray([]);
 * // => false
 */
var isTypedArray = nodeIsTypedArray ? _baseUnary(nodeIsTypedArray) : _baseIsTypedArray;

var isTypedArray_1 = isTypedArray;

/** Used for built-in method references. */
var objectProto$6 = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty$4 = objectProto$6.hasOwnProperty;

/**
 * Creates an array of the enumerable property names of the array-like `value`.
 *
 * @private
 * @param {*} value The value to query.
 * @param {boolean} inherited Specify returning inherited property names.
 * @returns {Array} Returns the array of property names.
 */
function arrayLikeKeys(value, inherited) {
  var isArr = isArray_1(value),
      isArg = !isArr && isArguments_1(value),
      isBuff = !isArr && !isArg && isBuffer_1(value),
      isType = !isArr && !isArg && !isBuff && isTypedArray_1(value),
      skipIndexes = isArr || isArg || isBuff || isType,
      result = skipIndexes ? _baseTimes(value.length, String) : [],
      length = result.length;

  for (var key in value) {
    if ((inherited || hasOwnProperty$4.call(value, key)) &&
        !(skipIndexes && (
           // Safari 9 has enumerable `arguments.length` in strict mode.
           key == 'length' ||
           // Node.js 0.10 has enumerable non-index properties on buffers.
           (isBuff && (key == 'offset' || key == 'parent')) ||
           // PhantomJS 2 has enumerable non-index properties on typed arrays.
           (isType && (key == 'buffer' || key == 'byteLength' || key == 'byteOffset')) ||
           // Skip index properties.
           _isIndex(key, length)
        ))) {
      result.push(key);
    }
  }
  return result;
}

var _arrayLikeKeys = arrayLikeKeys;

/**
 * Creates a unary function that invokes `func` with its argument transformed.
 *
 * @private
 * @param {Function} func The function to wrap.
 * @param {Function} transform The argument transform.
 * @returns {Function} Returns the new function.
 */
function overArg(func, transform) {
  return function(arg) {
    return func(transform(arg));
  };
}

var _overArg = overArg;

/* Built-in method references for those with the same name as other `lodash` methods. */
var nativeKeys = _overArg(Object.keys, Object);

var _nativeKeys = nativeKeys;

/** Used for built-in method references. */
var objectProto$7 = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty$5 = objectProto$7.hasOwnProperty;

/**
 * The base implementation of `_.keys` which doesn't treat sparse arrays as dense.
 *
 * @private
 * @param {Object} object The object to query.
 * @returns {Array} Returns the array of property names.
 */
function baseKeys(object) {
  if (!_isPrototype(object)) {
    return _nativeKeys(object);
  }
  var result = [];
  for (var key in Object(object)) {
    if (hasOwnProperty$5.call(object, key) && key != 'constructor') {
      result.push(key);
    }
  }
  return result;
}

var _baseKeys = baseKeys;

/**
 * Creates an array of the own enumerable property names of `object`.
 *
 * **Note:** Non-object values are coerced to objects. See the
 * [ES spec](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
 * for more details.
 *
 * @static
 * @since 0.1.0
 * @memberOf _
 * @category Object
 * @param {Object} object The object to query.
 * @returns {Array} Returns the array of property names.
 * @example
 *
 * function Foo() {
 *   this.a = 1;
 *   this.b = 2;
 * }
 *
 * Foo.prototype.c = 3;
 *
 * _.keys(new Foo);
 * // => ['a', 'b'] (iteration order is not guaranteed)
 *
 * _.keys('hi');
 * // => ['0', '1']
 */
function keys(object) {
  return isArrayLike_1(object) ? _arrayLikeKeys(object) : _baseKeys(object);
}

var keys_1 = keys;

/** Used for built-in method references. */
var objectProto$8 = Object.prototype;

/** Used to check objects for own properties. */
var hasOwnProperty$6 = objectProto$8.hasOwnProperty;

/**
 * Assigns own enumerable string keyed properties of source objects to the
 * destination object. Source objects are applied from left to right.
 * Subsequent sources overwrite property assignments of previous sources.
 *
 * **Note:** This method mutates `object` and is loosely based on
 * [`Object.assign`](https://mdn.io/Object/assign).
 *
 * @static
 * @memberOf _
 * @since 0.10.0
 * @category Object
 * @param {Object} object The destination object.
 * @param {...Object} [sources] The source objects.
 * @returns {Object} Returns `object`.
 * @see _.assignIn
 * @example
 *
 * function Foo() {
 *   this.a = 1;
 * }
 *
 * function Bar() {
 *   this.c = 3;
 * }
 *
 * Foo.prototype.b = 2;
 * Bar.prototype.d = 4;
 *
 * _.assign({ 'a': 0 }, new Foo, new Bar);
 * // => { 'a': 1, 'c': 3 }
 */
var assign = _createAssigner(function(object, source) {
  if (_isPrototype(source) || isArrayLike_1(source)) {
    _copyObject(source, keys_1(source), object);
    return;
  }
  for (var key in source) {
    if (hasOwnProperty$6.call(source, key)) {
      _assignValue(object, key, source[key]);
    }
  }
});

var assign_1 = assign;

var createTransitionManager = function createTransitionManager() {
  var prompt = null;

  var setPrompt = function setPrompt(nextPrompt) {
    warning_1(prompt == null, 'A history supports only one prompt at a time');
    prompt = nextPrompt;
    return function () {
      if (prompt === nextPrompt) prompt = null;
    };
  };

  var confirmTransitionTo = function confirmTransitionTo(location, action, getUserConfirmation, callback) {
    // TODO: If another transition starts while we're still confirming
    // the previous one, we may end up in a weird state. Figure out the
    // best way to handle this.
    if (prompt !== null) {
      var result = typeof prompt === 'function' ? prompt(location, action) : prompt;

      if (typeof result === 'string') {
        if (typeof getUserConfirmation === 'function') {
          getUserConfirmation(result, callback);
        } else {
          warning_1(false, 'A history needs a getUserConfirmation function in order to use a prompt message');
          callback(true);
        }
      } else {
        // Return false from a transition hook to cancel the transition.
        callback(result !== false);
      }
    } else {
      callback(true);
    }
  };

  var listeners = [];

  var appendListener = function appendListener(fn) {
    var isActive = true;

    var listener = function listener() {
      if (isActive) fn.apply(void 0, arguments);
    };

    listeners.push(listener);
    return function () {
      isActive = false;
      listeners = listeners.filter(function (item) {
        return item !== listener;
      });
    };
  };

  var notifyListeners = function notifyListeners() {
    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    listeners.forEach(function (listener) {
      return listener.apply(void 0, args);
    });
  };

  return {
    setPrompt: setPrompt,
    confirmTransitionTo: confirmTransitionTo,
    appendListener: appendListener,
    notifyListeners: notifyListeners
  };
};

function isAbsolute(pathname) {
  return pathname.charAt(0) === '/';
}

// About 1.5x faster than the two-arg version of Array#splice()
function spliceOne(list, index) {
  for (var i = index, k = i + 1, n = list.length; k < n; i += 1, k += 1) {
    list[i] = list[k];
  }

  list.pop();
}

// This implementation is based heavily on node's url.parse
function resolvePathname(to) {
  var from = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : '';

  var toParts = to && to.split('/') || [];
  var fromParts = from && from.split('/') || [];

  var isToAbs = to && isAbsolute(to);
  var isFromAbs = from && isAbsolute(from);
  var mustEndAbs = isToAbs || isFromAbs;

  if (to && isAbsolute(to)) {
    // to is absolute
    fromParts = toParts;
  } else if (toParts.length) {
    // to is relative, drop the filename
    fromParts.pop();
    fromParts = fromParts.concat(toParts);
  }

  if (!fromParts.length) return '/';

  var hasTrailingSlash = void 0;
  if (fromParts.length) {
    var last = fromParts[fromParts.length - 1];
    hasTrailingSlash = last === '.' || last === '..' || last === '';
  } else {
    hasTrailingSlash = false;
  }

  var up = 0;
  for (var i = fromParts.length; i >= 0; i--) {
    var part = fromParts[i];

    if (part === '.') {
      spliceOne(fromParts, i);
    } else if (part === '..') {
      spliceOne(fromParts, i);
      up++;
    } else if (up) {
      spliceOne(fromParts, i);
      up--;
    }
  }

  if (!mustEndAbs) for (; up--; up) {
    fromParts.unshift('..');
  }if (mustEndAbs && fromParts[0] !== '' && (!fromParts[0] || !isAbsolute(fromParts[0]))) fromParts.unshift('');

  var result = fromParts.join('/');

  if (hasTrailingSlash && result.substr(-1) !== '/') result += '/';

  return result;
}

var addLeadingSlash = function addLeadingSlash(path) {
  return path.charAt(0) === '/' ? path : '/' + path;
};
var stripLeadingSlash = function stripLeadingSlash(path) {
  return path.charAt(0) === '/' ? path.substr(1) : path;
};
var hasBasename = function hasBasename(path, prefix) {
  return new RegExp('^' + prefix + '(\\/|\\?|#|$)', 'i').test(path);
};
var stripBasename = function stripBasename(path, prefix) {
  return hasBasename(path, prefix) ? path.substr(prefix.length) : path;
};
var stripTrailingSlash = function stripTrailingSlash(path) {
  return path.charAt(path.length - 1) === '/' ? path.slice(0, -1) : path;
};
var parsePath = function parsePath(path) {
  var pathname = path || '/';
  var search = '';
  var hash = '';
  var hashIndex = pathname.indexOf('#');

  if (hashIndex !== -1) {
    hash = pathname.substr(hashIndex);
    pathname = pathname.substr(0, hashIndex);
  }

  var searchIndex = pathname.indexOf('?');

  if (searchIndex !== -1) {
    search = pathname.substr(searchIndex);
    pathname = pathname.substr(0, searchIndex);
  }

  return {
    path: pathname,
    search: search === '?' ? '' : search,
    hash: hash === '#' ? '' : hash
  };
};
var createPath = function createPath(location) {
  var path = location.path,
      search = location.search,
      hash = location.hash;
  var pathname = path || '/';

  if (search && search !== '?') {
    pathname += search.charAt(0) === '?' ? search : "?".concat(search);
  }

  if (hash && hash !== '#') pathname += hash.charAt(0) === '#' ? hash : "#".concat(hash);
  return pathname;
};

function createLocation(path, key, currentLocation) {
  var location;
  var tmpLocation = parsePath(path);
  location = assign_1({}, tmpLocation, {
    state: {
      key: key
    }
  });
  location.state = {
    key: key
  };
  var params = {};
  var searchString = location.search;

  if (searchString.length > 0) {
    var queryString = searchString.substring(1);
    queryString.split('&').forEach(function (pair) {
      if (pair.indexOf('=') === -1) return;

      var _pair$split = pair.split('='),
          _pair$split2 = _slicedToArray(_pair$split, 2),
          key = _pair$split2[0],
          value = _pair$split2[1];

      params[key] = value;
    });
  }

  location.params = params;

  if (currentLocation) {
    // Resolve incomplete/relative pathname relative to current location.
    if (!location.path) {
      location.path = currentLocation.path;
    } else if (location.path.charAt(0) !== '/') {
      location.path = resolvePathname(location.path, currentLocation.path);
    }
  } else {
    // When there is no prior location and pathname is empty, set it to /
    if (!location.path) {
      location.path = '/';
    }
  }

  return location;
}

var tryToCall = function tryToCall(func) {
  var ctx = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : null;
  if (!func) return;

  for (var _len = arguments.length, args = new Array(_len > 2 ? _len - 2 : 0), _key = 2; _key < _len; _key++) {
    args[_key - 2] = arguments[_key];
  }

  if (ctx) {
    return func.apply(ctx, args);
  } else {
    return func.apply(void 0, args);
  }
};

var PopStateEvent = 'popstate';
var defaultStoreKey = 'taroRouterStore';
var globalHistory = window.history;

var getHashPath = function getHashPath() {
  var href = window.location.href;
  var hashIndex = href.indexOf('#');
  return hashIndex === -1 ? '' : href.substring(hashIndex + 1);
};

var stateKey = 0;
/**
 * 获取state key
 */

var createKey = function createKey() {
  return String(++stateKey);
};

var getHistoryState = function getHistoryState() {
  try {
    var state = globalHistory.state || {};

    if (typeof state.key !== 'string') {
      state.key = String(stateKey);
    } else {
      stateKey = state.key;
    }

    return state;
  } catch (e) {
    // IE 11 sometimes throws when accessing window.history.state
    // See https://github.com/ReactTraining/history/pull/289
    return {
      key: String(stateKey)
    };
  }
};

var tryToParseStore = function tryToParseStore(state) {
  var store = {
    key: '0'
  };

  try {
    var storeObj = JSON.parse(localStorage.getItem(defaultStoreKey));

    if (_typeof(storeObj) === 'object' && typeof storeObj.key === 'string') {
      store = storeObj;
    }
  } catch (e) {}

  var isValid = store.key === state.key; // warning(isValid, 'Invalid location store, it is rewrote')

  if (!isValid) {
    store.key = state.key;
  }

  return store;
};
/**
 * 创建对象序列化的函数
 *
 * @param storeObj 需要序列化的对象引用
 */


var createHistorySerializer = function createHistorySerializer(storeObj) {
  var serialize = function serialize() {
    try {
      localStorage.setItem(defaultStoreKey, JSON.stringify(storeObj));
    } catch (e) {}
  };

  serialize();
  return serialize;
};

var createHistory = function createHistory(props) {
  var transitionManager = createTransitionManager();
  transitionManager.setPrompt('');
  var basename = props.basename ? stripTrailingSlash(addLeadingSlash(props.basename)) : '';
  var customRoutes = props.customRoutes || {};
  var listenerCount = 0;
  var serialize;
  props.mode = props.mode || "hash";

  var getDOMLocation = function getDOMLocation(historyState) {
    var key = historyState.key;
    var _window$location = window.location,
        pathname = _window$location.pathname,
        search = _window$location.search,
        hash = _window$location.hash;
    var path = props.mode === "hash" ? addLeadingSlash(getHashPath()) : pathname + search + hash;

    if (props.mode === 'browser') {
      warning_1(hasBasename(path, basename), 'You are attempting to use a basename on a page whose URL path does not begin ' + 'with the basename. Expected path "' + path + '" to begin with "' + basename + '".');
    }

    path = stripBasename(path, basename);

    if (path === '/') {
      path = props.firstPagePath + search + hash;
    }

    return createLocation(path, key);
  };

  var initState = getHistoryState();
  var initialLocation = getDOMLocation(initState);
  var lastLocation = initialLocation;
  Taro._$router = initialLocation;
  var store = tryToParseStore(initState);
  serialize = createHistorySerializer(store);
  globalHistory.replaceState(initialLocation.state, '');
  var createHref = props.mode === "hash" ? function (location) {
    return '#' + addLeadingSlash(basename + createPath(location));
  } : function (location) {
    return basename + createPath(location);
  };

  var setState = function setState(nextState) {
    assign_1(history, nextState);
    var fromLocation = Object.assign({}, lastLocation); // 记录最后一个location，浏览器前进后退按钮用

    lastLocation = Object.assign({}, nextState.location);
    stateKey = Number(nextState.location.state.key);
    serialize();
    history.length = globalHistory.length;
    var params = {
      fromLocation: fromLocation,
      toLocation: history.location,
      action: history.action
    };
    Taro._$router = history.location;
    Taro.eventCenter.trigger('__taroRouterChange', Object.assign({}, params));
    transitionManager.notifyListeners(Object.assign({}, params));
  };

  function getCurrentRoute() {
    if (Taro && typeof Taro.getCurrentPages === 'function') {
      var currentPageStack = Taro.getCurrentPages();
      var stackTop = currentPageStack.length - 1;
      return currentPageStack[stackTop];
    }

    return {};
  }

  function getUserConfirmation(next, fromLocation, toLocation) {
    var currentRoute = getCurrentRoute() || {};
    var leaveHook = currentRoute.beforeRouteLeave;

    if (typeof leaveHook === 'function') {
      tryToCall(leaveHook, currentRoute, fromLocation, toLocation, next);
    } else {
      next(true);
    }
  }

  var push = function push(path) {
    var action = 'PUSH';
    var key = createKey();
    var location = createLocation(path, key, history.location);
    var originalPath = location.path;

    if (originalPath in customRoutes) {
      location.path = customRoutes[originalPath];
    }

    transitionManager.confirmTransitionTo(location, action, function (result, callback) {
      getUserConfirmation(callback, lastLocation, location);
    }, function (ok) {
      if (!ok) {
        stateKey--;
        return;
      }

      var href = createHref(location);
      globalHistory.pushState({
        key: key
      }, '', href);
      store.key = key;
      setState({
        action: action,
        location: location
      });
    });
  };

  var replace = function replace(path) {
    var action = 'REPLACE';
    var key = store.key;
    var location = createLocation(path, key, history.location);
    var originalPath = location.path;

    if (originalPath in customRoutes) {
      location.path = customRoutes[originalPath];
    }

    transitionManager.confirmTransitionTo(location, action, function (result, callback) {
      getUserConfirmation(callback, lastLocation, location);
    }, function (ok) {
      if (!ok) return;
      var href = createHref(location);
      globalHistory.replaceState({
        key: key
      }, '', href);
      setState({
        action: action,
        location: location
      });
    });
  };

  var go = function go(num) {
    globalHistory.go(num);
  };

  var goBack = function goBack() {
    return go(-1);
  };

  var goForward = function goForward() {
    return go(1);
  };

  var handlePopState = function handlePopState(e) {
    // history.pushState和history.replaceState不会触发这个事件
    // 仅在浏览器前进后退操作、history.go/back/forward调用、hashchange的时候触发
    // 这里的window.location已经是新的了
    var state = e.state;

    if (!state) {
      state = {
        key: createKey()
      };
      globalHistory.replaceState(state, '', '');
    }

    var currentKey = Number(lastLocation.state.key);
    var nextKey = Number(state.key);
    var nextLocation = getDOMLocation(state);
    var action;

    if (nextKey > currentKey) {
      action = 'PUSH';
    } else if (nextKey < currentKey) {
      action = 'POP';
    } else {
      action = 'REPLACE';
    }

    store.key = String(nextKey);
    transitionManager.confirmTransitionTo(nextLocation, action, function (result, callback) {
      getUserConfirmation(callback, lastLocation, nextLocation);
    }, function (ok) {
      if (ok) {
        setState({
          action: action,
          location: nextLocation
        });
      } else {
        revertPop();
      }
    });
  };

  var revertPop = function revertPop() {
    var toLocation = history.location;
    var key = toLocation.state.key;
    var href = createHref(toLocation);
    globalHistory.pushState({
      key: key
    }, '', href);
  };

  var checkDOMListeners = function checkDOMListeners(delta) {
    listenerCount += delta;

    if (listenerCount === 1) {
      var isSafari = /^((?!chrome).)*safari/i.test(navigator.userAgent);

      if (isSafari) {
        window.addEventListener('load', function () {
          setTimeout(function () {
            window.addEventListener(PopStateEvent, handlePopState);
          }, 0);
        });
      } else {
        window.addEventListener(PopStateEvent, handlePopState);
      }
    } else if (listenerCount === 0) {
      window.removeEventListener(PopStateEvent, handlePopState);
    }
  };

  var listen = function listen(listener) {
    var unlisten = transitionManager.appendListener(listener);
    checkDOMListeners(1);
    return function () {
      checkDOMListeners(-1);
      unlisten();
    };
  };

  var isBlocked = false;

  var block = function block() {
    var prompt = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : false;
    var unblock = transitionManager.setPrompt(prompt);

    if (!isBlocked) {
      checkDOMListeners(1);
      isBlocked = true;
    }

    return function () {
      if (isBlocked) {
        isBlocked = false;
        checkDOMListeners(-1);
      }

      return unblock();
    };
  };

  var history = {
    action: 'POP',
    block: block,
    createHref: createHref,
    go: go,
    goBack: goBack,
    goForward: goForward,
    length: globalHistory.length,
    listen: listen,
    location: initialLocation,
    push: push,
    replace: replace
  };
  return history;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

/**
 * Use invariant() to assert state which your program assumes to be true.
 *
 * Provide sprintf-style format (only %s is supported) and arguments
 * to provide information about what broke and what you were
 * expecting.
 *
 * The invariant message will be stripped in production, but the invariant
 * will remain to ensure logic does not differ in production.
 */

var NODE_ENV = process.env.NODE_ENV;

var invariant = function(condition, format, a, b, c, d, e, f) {
  if (NODE_ENV !== 'production') {
    if (format === undefined) {
      throw new Error('invariant requires an error message argument');
    }
  }

  if (!condition) {
    var error;
    if (format === undefined) {
      error = new Error(
        'Minified exception occurred; use the non-minified dev environment ' +
        'for the full error message and additional helpful warnings.'
      );
    } else {
      var args = [a, b, c, d, e, f];
      var argIndex = 0;
      error = new Error(
        format.replace(/%s/g, function() { return args[argIndex++]; })
      );
      error.name = 'Invariant Violation';
    }

    error.framesToPop = 1; // we don't care about invariant's own frame
    throw error;
  }
};

var invariant_1 = invariant;

/**
 * A specialized version of `_.map` for arrays without support for iteratee
 * shorthands.
 *
 * @private
 * @param {Array} [array] The array to iterate over.
 * @param {Function} iteratee The function invoked per iteration.
 * @returns {Array} Returns the new mapped array.
 */
function arrayMap(array, iteratee) {
  var index = -1,
      length = array == null ? 0 : array.length,
      result = Array(length);

  while (++index < length) {
    result[index] = iteratee(array[index], index, array);
  }
  return result;
}

var _arrayMap = arrayMap;

/**
 * The base implementation of `_.toPairs` and `_.toPairsIn` which creates an array
 * of key-value pairs for `object` corresponding to the property names of `props`.
 *
 * @private
 * @param {Object} object The object to query.
 * @param {Array} props The property names to get values for.
 * @returns {Object} Returns the key-value pairs.
 */
function baseToPairs(object, props) {
  return _arrayMap(props, function(key) {
    return [key, object[key]];
  });
}

var _baseToPairs = baseToPairs;

/* Built-in method references that are verified to be native. */
var DataView = _getNative(_root, 'DataView');

var _DataView = DataView;

/* Built-in method references that are verified to be native. */
var Map$1 = _getNative(_root, 'Map');

var _Map = Map$1;

/* Built-in method references that are verified to be native. */
var Promise$1 = _getNative(_root, 'Promise');

var _Promise = Promise$1;

/* Built-in method references that are verified to be native. */
var Set = _getNative(_root, 'Set');

var _Set = Set;

/* Built-in method references that are verified to be native. */
var WeakMap$1 = _getNative(_root, 'WeakMap');

var _WeakMap = WeakMap$1;

/** `Object#toString` result references. */
var mapTag$1 = '[object Map]',
    objectTag$1 = '[object Object]',
    promiseTag = '[object Promise]',
    setTag$1 = '[object Set]',
    weakMapTag$1 = '[object WeakMap]';

var dataViewTag$1 = '[object DataView]';

/** Used to detect maps, sets, and weakmaps. */
var dataViewCtorString = _toSource(_DataView),
    mapCtorString = _toSource(_Map),
    promiseCtorString = _toSource(_Promise),
    setCtorString = _toSource(_Set),
    weakMapCtorString = _toSource(_WeakMap);

/**
 * Gets the `toStringTag` of `value`.
 *
 * @private
 * @param {*} value The value to query.
 * @returns {string} Returns the `toStringTag`.
 */
var getTag = _baseGetTag;

// Fallback for data views, maps, sets, and weak maps in IE 11 and promises in Node.js < 6.
if ((_DataView && getTag(new _DataView(new ArrayBuffer(1))) != dataViewTag$1) ||
    (_Map && getTag(new _Map) != mapTag$1) ||
    (_Promise && getTag(_Promise.resolve()) != promiseTag) ||
    (_Set && getTag(new _Set) != setTag$1) ||
    (_WeakMap && getTag(new _WeakMap) != weakMapTag$1)) {
  getTag = function(value) {
    var result = _baseGetTag(value),
        Ctor = result == objectTag$1 ? value.constructor : undefined,
        ctorString = Ctor ? _toSource(Ctor) : '';

    if (ctorString) {
      switch (ctorString) {
        case dataViewCtorString: return dataViewTag$1;
        case mapCtorString: return mapTag$1;
        case promiseCtorString: return promiseTag;
        case setCtorString: return setTag$1;
        case weakMapCtorString: return weakMapTag$1;
      }
    }
    return result;
  };
}

var _getTag = getTag;

/**
 * Converts `map` to its key-value pairs.
 *
 * @private
 * @param {Object} map The map to convert.
 * @returns {Array} Returns the key-value pairs.
 */
function mapToArray(map) {
  var index = -1,
      result = Array(map.size);

  map.forEach(function(value, key) {
    result[++index] = [key, value];
  });
  return result;
}

var _mapToArray = mapToArray;

/**
 * Converts `set` to its value-value pairs.
 *
 * @private
 * @param {Object} set The set to convert.
 * @returns {Array} Returns the value-value pairs.
 */
function setToPairs(set) {
  var index = -1,
      result = Array(set.size);

  set.forEach(function(value) {
    result[++index] = [value, value];
  });
  return result;
}

var _setToPairs = setToPairs;

/** `Object#toString` result references. */
var mapTag$2 = '[object Map]',
    setTag$2 = '[object Set]';

/**
 * Creates a `_.toPairs` or `_.toPairsIn` function.
 *
 * @private
 * @param {Function} keysFunc The function to get the keys of a given object.
 * @returns {Function} Returns the new pairs function.
 */
function createToPairs(keysFunc) {
  return function(object) {
    var tag = _getTag(object);
    if (tag == mapTag$2) {
      return _mapToArray(object);
    }
    if (tag == setTag$2) {
      return _setToPairs(object);
    }
    return _baseToPairs(object, keysFunc(object));
  };
}

var _createToPairs = createToPairs;

/**
 * Creates an array of own enumerable string keyed-value pairs for `object`
 * which can be consumed by `_.fromPairs`. If `object` is a map or set, its
 * entries are returned.
 *
 * @static
 * @memberOf _
 * @since 4.0.0
 * @alias entries
 * @category Object
 * @param {Object} object The object to query.
 * @returns {Array} Returns the key-value pairs.
 * @example
 *
 * function Foo() {
 *   this.a = 1;
 *   this.b = 2;
 * }
 *
 * Foo.prototype.c = 3;
 *
 * _.toPairs(new Foo);
 * // => [['a', 1], ['b', 2]] (iteration order is not guaranteed)
 */
var toPairs = _createToPairs(keys_1);

var toPairs_1 = toPairs;

var createWrappedComponent = function createWrappedComponent(component) {
  var WrappedComponent = /*#__PURE__*/function (_component) {
    _inherits(WrappedComponent, _component);

    var _super = _createSuper(WrappedComponent);

    function WrappedComponent(props, context) {
      var _this;

      _classCallCheck(this, WrappedComponent);

      _this = _super.call(this, props, context);
      var originalComponentDidShow = _this.componentDidShow;

      var newComponentDidShow = function newComponentDidShow() {
        var _ref = this.config || {
          navigationBarTitleText: null
        },
            navigationBarTitleText = _ref.navigationBarTitleText;

        if (navigationBarTitleText) {
          document.title = navigationBarTitleText;
        }

        tryToCall(originalComponentDidShow, this);
      };

      _this.componentDidShow = newComponentDidShow;
      return _this;
    }

    _createClass(WrappedComponent, [{
      key: "componentDidMount",
      value: function componentDidMount() {
        var superComponentDidMount = _get(_getPrototypeOf(WrappedComponent.prototype), "componentDidMount", this);

        tryToCall(superComponentDidMount, this);
        tryToCall(this.componentDidShow, this);
      }
    }, {
      key: "componentWillUnmount",
      value: function componentWillUnmount() {
        var componentDidHide = this.componentDidHide;

        var superComponentWillUnmount = _get(_getPrototypeOf(WrappedComponent.prototype), "componentWillUnmount", this);

        tryToCall(superComponentWillUnmount, this);
        tryToCall(componentDidHide, this);
      }
    }]);

    return WrappedComponent;
  }(component);

  return WrappedComponent;
};

var getScroller = function getScroller() {
  var panel = document.querySelector('.taro-tabbar__panel');
  var res;

  if (panel) {
    res = {
      set: function set(pos) {
        panel.scrollTop = pos;
      },
      get: function get() {
        return panel.scrollTop;
      }
    };
  } else {
    res = {
      set: function set(pos) {
        return window.scrollTo(0, pos);
      },
      get: function get() {
        return window.pageYOffset;
      }
    };
  }

  return res;
};

var scroller;

var Route = /*#__PURE__*/function (_Taro$Component) {
  _inherits(Route, _Taro$Component);

  var _super = _createSuper(Route);

  function Route(props, context) {
    var _this;

    _classCallCheck(this, Route);

    _this = _super.call(this, props, context);
    _this.matched = false;
    _this.isRoute = true;
    _this.scrollPos = 0;
    _this.state = {
      location: {}
    };

    _this.getWrapRef = function (ref) {
      if (ref) _this.containerRef = ref;
    };

    _this.getRef = function (ref) {
      if (ref) {
        if (ref.props.location !== _this.state.location) {
          ref.props.location = _this.state.location;
        }

        _this.componentRef = ref;

        _this.props.collectComponent(ref, _this.props.key);
      }
    };

    _this.matched = _this.computeMatch(_this.props.currentLocation);

    if (_this.matched) {
      _this.state = {
        location: _this.props.currentLocation
      };
    }

    return _this;
  }

  _createClass(Route, [{
    key: "computeMatch",
    value: function computeMatch(currentLocation) {
      var path = currentLocation.path;
      var key = currentLocation.state.key;
      var isIndex = this.props.isIndex;
      var isTabBar = this.props.isTabBar;

      if (key !== undefined) {
        if (isTabBar) {
          return key === this.props.key && path === this.props.path;
        } else {
          return key === this.props.key;
        }
      } else {
        return isIndex && path === '/';
      }
    }
  }, {
    key: "updateComponent",
    value: function updateComponent() {
      var _this2 = this;

      var props = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : this.props;

      if (this.matched && this.componentRef) {
        this.setState({
          location: props.currentLocation
        }, function () {
          _this2.componentRef.props.location = _this2.state.location;
        });
      }

      props.componentLoader().then(function (_ref) {
        var component = _ref.default;

        if (!component) {
          throw Error("Received a falsy component for route \"".concat(props.path, "\". Forget to export it?"));
        }

        var WrappedComponent = createWrappedComponent(component);
        _this2.wrappedComponent = WrappedComponent;

        _this2.forceUpdate();
      }).catch(function (e) {
        console.error(e);
      });
    }
  }, {
    key: "componentDidMount",
    value: function componentDidMount() {
      scroller = scroller || getScroller();
      scroller.set(0);
      this.updateComponent();
    }
  }, {
    key: "componentWillReceiveProps",
    value: function componentWillReceiveProps(nProps) {
      var _this3 = this;

      var isRedirect = nProps.isRedirect;
      var lastMatched = this.matched;
      var nextMatched = this.computeMatch(nProps.currentLocation);

      if (isRedirect) {
        this.updateComponent(nProps);
      } else if (lastMatched === nextMatched) {
        return;
      }

      this.matched = nextMatched;

      if (nextMatched) {
        if (!isRedirect) {
          Nerv.nextTick(function () {
            _this3.showPage();

            scroller = scroller || getScroller();
            scroller.set(_this3.scrollPos);
          });
          tryToCall(this.componentRef.componentDidShow, this.componentRef);
        }
      } else {
        scroller = scroller || getScroller();
        this.scrollPos = scroller.get();
        Nerv.nextTick(function () {
          _this3.hidePage();

          tryToCall(_this3.componentRef.componentDidHide, _this3.componentRef);
        });
      }
    }
  }, {
    key: "shouldComponentUpdate",
    value: function shouldComponentUpdate() {
      /* 防止route的props变化导致组件重新渲染 */
      return false;
    }
  }, {
    key: "showPage",
    value: function showPage() {
      var dom = this.containerRef;

      if (!dom) {
        return console.error("showPage:fail Received a falsy component for route \"".concat(this.props.path, "\". Forget to export it?"));
      }

      dom.style.display = 'block';
    }
  }, {
    key: "hidePage",
    value: function hidePage() {
      var dom = this.containerRef;

      if (!dom) {
        return console.error("hidePage:fail Received a falsy component for route \"".concat(this.props.path, "\". Forget to export it?"));
      }

      dom.style.display = 'none';
    }
  }, {
    key: "render",
    value: function render() {
      if (!this.wrappedComponent) return null;
      var WrappedComponent = this.wrappedComponent;
      return Nerv__default.createElement("div", {
        className: "taro_page",
        ref: this.getWrapRef,
        style: {
          minHeight: '100%'
        }
      }, Nerv__default.createElement(WrappedComponent, {
        ref: this.getRef,
        location: this.state.location
      }));
    }
  }]);

  return Route;
}(Taro.Component);

var Router = /*#__PURE__*/function (_Taro$Component) {
  _inherits(Router, _Taro$Component);

  var _super = _createSuper(Router);

  function Router() {
    var _this;

    _classCallCheck(this, Router);

    _this = _super.apply(this, arguments);
    _this.currentPages = [];
    _this.customRoutes = [];
    _this.state = {
      location: _this.props.history.location,
      routeStack: []
    };

    _this.collectComponent = function (comp, index) {
      _this.currentPages[Number(index) || 0] = comp;
    };

    return _this;
  }

  _createClass(Router, [{
    key: "mountApis",
    value: function mountApis() {
      var _this2 = this;

      // 挂载Apis
      Taro.getCurrentPages = function () {
        return _this2.currentPages;
      };
    }
  }, {
    key: "computeMatch",
    value: function computeMatch(location) {
      // 找出匹配的路由组件
      var originalPathname = location.path;
      var pathname = originalPathname;

      if (this.props.mode === 'multi') {
        return this.props.routes[0];
      } else {
        var foundRoute = this.customRoutes.filter(function (_ref) {
          var _ref2 = _slicedToArray(_ref, 2),
              originalRoute = _ref2[0],
              mappedRoute = _ref2[1];

          return originalPathname === mappedRoute;
        });

        if (foundRoute.length) {
          pathname = foundRoute[0][0];
        }

        var matchedRoute = this.props.routes.filter(function (_ref3) {
          var path = _ref3.path,
              isIndex = _ref3.isIndex;
          if (isIndex && pathname === '/') return true;
          return pathname === path;
        });

        if (!matchedRoute[0] && Taro['_$app'] && Taro['_$app'].componentDidNotFound) {
          Taro['_$app'].componentDidNotFound.call(Taro['_$app'], {
            path: pathname,
            query: location.params
          });
        }

        invariant_1(matchedRoute[0], "Can not find proper registered route for '".concat(pathname, "'"));
        return matchedRoute[0];
      }
    }
  }, {
    key: "isTabBar",
    value: function isTabBar(path) {
      var tabBar = this.props.tabBar;

      if (path && tabBar && tabBar.list && tabBar.list instanceof Array) {
        return tabBar.list.findIndex(function (e) {
          return e.pagePath === path;
        }) !== -1;
      }

      return false;
    }
  }, {
    key: "push",
    value: function push(toLocation) {
      var isTabBar = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false;

      var routeStack = _toConsumableArray(this.state.routeStack);

      var matchedRoute = this.computeMatch(toLocation);
      routeStack.forEach(function (v) {
        v.isRedirect = false;
      });
      routeStack.push(assign_1({}, matchedRoute, {
        key: toLocation.state.key,
        isRedirect: false,
        isTabBar: isTabBar
      }));
      this.setState({
        routeStack: routeStack,
        location: toLocation
      });
    }
  }, {
    key: "pop",
    value: function pop(toLocation, fromLocation) {
      var routeStack = _toConsumableArray(this.state.routeStack);

      var fromKey = Number(fromLocation.state.key);
      var toKey = Number(toLocation.state.key);
      var delta = toKey - fromKey;
      routeStack.splice(delta);

      if (routeStack.length === 0) {
        // 不存在历史栈, 需要重新构造
        var matchedRoute = this.computeMatch(toLocation);
        routeStack = [assign_1({}, matchedRoute, {
          key: toLocation.state.key,
          isRedirect: false
        })];
      }

      this.setState({
        routeStack: routeStack,
        location: toLocation
      });
    }
  }, {
    key: "replace",
    value: function replace(toLocation) {
      var routeStack = _toConsumableArray(this.state.routeStack);

      var matchedRoute = this.computeMatch(toLocation);
      routeStack.splice(-1, 1, assign_1({}, matchedRoute, {
        key: toLocation.state.key,
        isRedirect: true
      }));
      this.setState({
        routeStack: routeStack,
        location: toLocation
      });
    }
  }, {
    key: "switch",
    value: function _switch(toLocation) {
      var isTabBar = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false;

      var routeStack = _toConsumableArray(this.state.routeStack);

      var matchedRoute = this.computeMatch(toLocation);
      var index = routeStack.findIndex(function (e) {
        return e.path === toLocation.path;
      });

      if (index === -1) {
        routeStack.forEach(function (v) {
          v.isRedirect = false;
        });
        routeStack.push(assign_1({}, matchedRoute, {
          key: toLocation.state.key,
          isRedirect: false,
          isTabBar: isTabBar
        }));
      } else {
        toLocation.state.key = routeStack[index].key || '';
      }

      this.setState({
        routeStack: routeStack,
        location: toLocation
      });
    }
  }, {
    key: "componentDidMount",
    value: function componentDidMount() {
      var _this3 = this;

      var _this$props = this.props,
          history = _this$props.history,
          customRoutes = _this$props.customRoutes,
          mode = _this$props.mode;
      this.mountApis();
      this.customRoutes = toPairs_1(customRoutes);
      this.unlisten = history.listen(function (_ref4) {
        var fromLocation = _ref4.fromLocation,
            toLocation = _ref4.toLocation,
            action = _ref4.action;

        if (action === "POP") {
          _this3.pop(toLocation, fromLocation);
        } else if (_this3.isTabBar(toLocation.path)) {
          _this3.switch(toLocation, true);
        } else {
          if (action === "PUSH") {
            _this3.push(toLocation);
          } else {
            _this3.replace(toLocation);
          }
        }

        _this3.lastLocation = history.location;

        _this3.setState({
          location: history.location
        });
      });
      this.lastLocation = history.location;
      this.push(this.lastLocation, this.isTabBar(this.lastLocation.path));

      if (mode === 'multi') {
        this.unlisten();
      }
    }
  }, {
    key: "componentWillUpdate",
    value: function componentWillUpdate(nextProps, nextState) {
      if (Taro._$router) {
        this.currentPages.length = Number(Taro._$router.state.key) + 1;
      }
    }
  }, {
    key: "componentDidShow",
    value: function componentDidShow() {
      if (Taro._$router) {
        this.currentPages.length = Number(Taro._$router.state.key) + 1;
      }
    }
  }, {
    key: "componentWillUnmount",
    value: function componentWillUnmount() {
      var mode = this.props.mode;
      if (mode === 'multi') return;
      this.unlisten();
    }
  }, {
    key: "render",
    value: function render() {
      var _this4 = this;

      var currentLocation = Taro._$router;
      return Nerv__default.createElement("div", {
        className: "taro_router",
        style: {
          height: '100%'
        }
      }, this.state.routeStack.map(function (_ref5, k) {
        var path = _ref5.path,
            componentLoader = _ref5.componentLoader,
            isIndex = _ref5.isIndex,
            isTabBar = _ref5.isTabBar,
            key = _ref5.key,
            isRedirect = _ref5.isRedirect;
        return Nerv__default.createElement(Route, {
          path: path,
          currentLocation: currentLocation,
          componentLoader: componentLoader,
          isIndex: isIndex,
          key: key,
          k: k,
          isTabBar: isTabBar,
          isRedirect: isRedirect,
          collectComponent: _this4.collectComponent
        });
      }));
    }
  }]);

  return Router;
}(Taro.Component);

var basename = '';
var currentPagename = '';
var relaunchUrlKey = '__relaunchUrl';

var addHtmlExtname = function addHtmlExtname(str) {
  return /\.html\b/.test(str) ? str : "".concat(str, ".html");
};

var notTabbar = function notTabbar(url) {
  var path = url.split('?')[0];
  var app = Taro.getApp();

  if (app && app.config) {
    var config = app.config;

    if (config.tabBar && config.tabBar.list && config.tabBar.list instanceof Array) {
      return config.tabBar.list.findIndex(function (e) {
        return e.pagePath === path;
      }) === -1;
    }
  }

  return true;
};

var getTargetUrl = function getTargetUrl(url, customRoutes) {
  var matched = url.match(/([\s\S]*)(\?[\s\S]*)?/) || [];
  var pathname = matched[1] || '';
  var search = matched[2] || '';
  var targetUrl = resolvePathname(pathname, currentPagename);
  var nextPagename = addHtmlExtname(stripLeadingSlash(customRoutes[targetUrl] || targetUrl));
  return "".concat(basename, "/").concat(nextPagename).concat(search);
};

var createNavigateTo = function createNavigateTo(_ref, history) {
  var customRoutes = _ref.customRoutes;
  return function (_ref2) {
    var url = _ref2.url;
    var res = {
      errMsg: ''
    };

    try {
      invariant_1(url, 'navigateTo must be called with a url');
      invariant_1(notTabbar(url), 'can not navigateTo a tabbar page');

      if (/^(https?:)\/\//.test(url)) {
        window.location.assign(url);
      } else if (history) {
        history.push(url);
      } else {
        window.location.assign(getTargetUrl(url, customRoutes));
      }

      res.errMsg = 'navigateTo:ok';
      return Promise.resolve(res);
    } catch (e) {
      res.errMsg = "navigateTo:fail ".concat(e.message);
      return Promise.reject(res);
    }
  };
};

var createNavigateBack = function createNavigateBack(_ref3, history) {
  var customRoutes = _ref3.customRoutes;
  return function () {
    var opts = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    var res = {
      errMsg: ''
    };

    try {
      var _opts$delta = opts.delta,
          delta = _opts$delta === void 0 ? 1 : _opts$delta;
      invariant_1(delta >= 0, 'navigateBack must be called with a delta greater than 0');

      if (history) {
        history.go(-delta);
      } else {
        window.history.go(-delta);
      }

      res.errMsg = 'navigateBack:ok';
      return Promise.resolve(res);
    } catch (e) {
      res.errMsg = "navigateBack:fail ".concat(e.message);
      return Promise.reject(res);
    }
  };
};

var createRedirectTo = function createRedirectTo(_ref4, history) {
  var customRoutes = _ref4.customRoutes;
  return function (_ref5) {
    var url = _ref5.url;
    var res = {
      errMsg: ''
    };

    try {
      invariant_1(url, 'redirectTo must be called with a url'); // invariant(notTabbar(url), 'can not redirectTo a tabbar page')

      if (/^(https?:)\/\//.test(url)) {
        window.location.assign(url);
      }

      if (history) {
        history.replace(url);
      } else {
        window.location.replace(getTargetUrl(url, customRoutes));
      }

      res.errMsg = 'redirectTo:ok';
      return Promise.resolve(res);
    } catch (e) {
      res.errMsg = "redirectTo:fail ".concat(e.message);
      return Promise.reject(res);
    }
  };
};

var createReLaunch = function createReLaunch(_ref6, history) {
  var customRoutes = _ref6.customRoutes;

  try {
    var relaunchUrl = localStorage.getItem(relaunchUrlKey);

    if (relaunchUrl) {
      localStorage.setItem(relaunchUrlKey, '');
      location.replace(relaunchUrl);
    }
  } catch (e) {
    console.log(e.message);
  }

  return function (_ref7) {
    var url = _ref7.url;
    return new Promise(function (resolve, reject) {
      var res = {
        errMsg: ''
      };

      try {
        // setTimeout hack
        // 修复 history.go 之后，后面的代码不执行的问题
        setTimeout(function () {
          if (history) {
            if (/^(https?:)\/\//.test(url)) {
              window.location.assign(url);
            } else {
              history.replace(url);
            }
          } else {
            localStorage.setItem(relaunchUrlKey, getTargetUrl(url, customRoutes));
            window.history.go(-(window.history.length - 1));
          }

          res.errMsg = 'reLaunch:ok';
          resolve(res);
        }, 50);

        if (history) {
          history.go(-(history.length - 1));
        } else {
          window.history.go(-(window.history.length - 1));
        }
      } catch (e) {
        res.errMsg = "reLaunch:fail ".concat(e.message);
        reject(res);
      }
    });
  };
};

var mountApis = function mountApis(routerConfig, history) {
  currentPagename = routerConfig.currentPagename;
  basename = stripTrailingSlash(routerConfig.basename);
  Taro.navigateTo = createNavigateTo(routerConfig, history);
  Taro.navigateBack = createNavigateBack(routerConfig, history);
  Taro.redirectTo = createRedirectTo(routerConfig, history);
  Taro.reLaunch = createReLaunch(routerConfig, history);
};

exports.createHistory = createHistory;
exports.Router = Router;
exports.mountApis = mountApis;
