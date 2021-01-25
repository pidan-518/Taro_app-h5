import React, { useMemo } from 'react';
import { Image } from '@tarojs/components';

/*! *****************************************************************************
Copyright (c) Microsoft Corporation. All rights reserved.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License. You may obtain a copy of the
License at http://www.apache.org/licenses/LICENSE-2.0

THIS CODE IS PROVIDED ON AN *AS IS* BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
KIND, EITHER EXPRESS OR IMPLIED, INCLUDING WITHOUT LIMITATION ANY IMPLIED
WARRANTIES OR CONDITIONS OF TITLE, FITNESS FOR A PARTICULAR PURPOSE,
MERCHANTABLITY OR NON-INFRINGEMENT.

See the Apache Version 2.0 License for specific language governing permissions
and limitations under the License.
***************************************************************************** */

var __assign = function() {
    __assign = Object.assign || function __assign(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};

function createCommonjsModule(fn, basedir, module) {
	return module = {
	  path: basedir,
	  exports: {},
	  require: function (path, base) {
      return commonjsRequire(path, (base === undefined || base === null) ? module.path : base);
    }
	}, fn(module, module.exports), module.exports;
}

function commonjsRequire () {
	throw new Error('Dynamic requires are not currently supported by @rollup/plugin-commonjs');
}

var reactIs_production_min = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports,"__esModule",{value:!0});
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?Symbol.for("react.memo"):
60115,r=b?Symbol.for("react.lazy"):60116;function t(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case h:return a;default:return u}}case r:case q:case d:return u}}}function v(a){return t(a)===m}exports.typeOf=t;exports.AsyncMode=l;exports.ConcurrentMode=m;exports.ContextConsumer=k;exports.ContextProvider=h;exports.Element=c;exports.ForwardRef=n;
exports.Fragment=e;exports.Lazy=r;exports.Memo=q;exports.Portal=d;exports.Profiler=g;exports.StrictMode=f;exports.Suspense=p;exports.isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||"object"===typeof a&&null!==a&&(a.$$typeof===r||a.$$typeof===q||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n)};exports.isAsyncMode=function(a){return v(a)||t(a)===l};exports.isConcurrentMode=v;exports.isContextConsumer=function(a){return t(a)===k};
exports.isContextProvider=function(a){return t(a)===h};exports.isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};exports.isForwardRef=function(a){return t(a)===n};exports.isFragment=function(a){return t(a)===e};exports.isLazy=function(a){return t(a)===r};exports.isMemo=function(a){return t(a)===q};exports.isPortal=function(a){return t(a)===d};exports.isProfiler=function(a){return t(a)===g};exports.isStrictMode=function(a){return t(a)===f};
exports.isSuspense=function(a){return t(a)===p};
});

var reactIs_development = createCommonjsModule(function (module, exports) {



if (process.env.NODE_ENV !== "production") {
  (function() {

Object.defineProperty(exports, '__esModule', { value: true });

// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
// nor polyfill, then a plain number is used for performance.
var hasSymbol = typeof Symbol === 'function' && Symbol.for;

var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace;
var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;

function isValidElementType(type) {
  return typeof type === 'string' || typeof type === 'function' ||
  // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE);
}

/**
 * Forked from fbjs/warning:
 * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
 *
 * Only change is we use console.warn instead of console.error,
 * and do nothing when 'console' is not supported.
 * This really simplifies the code.
 * ---
 * Similar to invariant but only logs a warning if the condition is not met.
 * This can be used to log issues in development environments in critical
 * paths. Removing the logging code for production environments will keep the
 * same logic and follow the same code paths.
 */

var lowPriorityWarning = function () {};

{
  var printWarning = function (format) {
    for (var _len = arguments.length, args = Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      args[_key - 1] = arguments[_key];
    }

    var argIndex = 0;
    var message = 'Warning: ' + format.replace(/%s/g, function () {
      return args[argIndex++];
    });
    if (typeof console !== 'undefined') {
      console.warn(message);
    }
    try {
      // --- Welcome to debugging React ---
      // This error was thrown as a convenience so that you can use this stack
      // to find the callsite that caused this warning to fire.
      throw new Error(message);
    } catch (x) {}
  };

  lowPriorityWarning = function (condition, format) {
    if (format === undefined) {
      throw new Error('`lowPriorityWarning(condition, format, ...args)` requires a warning ' + 'message argument');
    }
    if (!condition) {
      for (var _len2 = arguments.length, args = Array(_len2 > 2 ? _len2 - 2 : 0), _key2 = 2; _key2 < _len2; _key2++) {
        args[_key2 - 2] = arguments[_key2];
      }

      printWarning.apply(undefined, [format].concat(args));
    }
  };
}

var lowPriorityWarning$1 = lowPriorityWarning;

function typeOf(object) {
  if (typeof object === 'object' && object !== null) {
    var $$typeof = object.$$typeof;
    switch ($$typeof) {
      case REACT_ELEMENT_TYPE:
        var type = object.type;

        switch (type) {
          case REACT_ASYNC_MODE_TYPE:
          case REACT_CONCURRENT_MODE_TYPE:
          case REACT_FRAGMENT_TYPE:
          case REACT_PROFILER_TYPE:
          case REACT_STRICT_MODE_TYPE:
          case REACT_SUSPENSE_TYPE:
            return type;
          default:
            var $$typeofType = type && type.$$typeof;

            switch ($$typeofType) {
              case REACT_CONTEXT_TYPE:
              case REACT_FORWARD_REF_TYPE:
              case REACT_PROVIDER_TYPE:
                return $$typeofType;
              default:
                return $$typeof;
            }
        }
      case REACT_LAZY_TYPE:
      case REACT_MEMO_TYPE:
      case REACT_PORTAL_TYPE:
        return $$typeof;
    }
  }

  return undefined;
}

// AsyncMode is deprecated along with isAsyncMode
var AsyncMode = REACT_ASYNC_MODE_TYPE;
var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
var ContextConsumer = REACT_CONTEXT_TYPE;
var ContextProvider = REACT_PROVIDER_TYPE;
var Element = REACT_ELEMENT_TYPE;
var ForwardRef = REACT_FORWARD_REF_TYPE;
var Fragment = REACT_FRAGMENT_TYPE;
var Lazy = REACT_LAZY_TYPE;
var Memo = REACT_MEMO_TYPE;
var Portal = REACT_PORTAL_TYPE;
var Profiler = REACT_PROFILER_TYPE;
var StrictMode = REACT_STRICT_MODE_TYPE;
var Suspense = REACT_SUSPENSE_TYPE;

var hasWarnedAboutDeprecatedIsAsyncMode = false;

// AsyncMode should be deprecated
function isAsyncMode(object) {
  {
    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
      hasWarnedAboutDeprecatedIsAsyncMode = true;
      lowPriorityWarning$1(false, 'The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
    }
  }
  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
}
function isConcurrentMode(object) {
  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
}
function isContextConsumer(object) {
  return typeOf(object) === REACT_CONTEXT_TYPE;
}
function isContextProvider(object) {
  return typeOf(object) === REACT_PROVIDER_TYPE;
}
function isElement(object) {
  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
}
function isForwardRef(object) {
  return typeOf(object) === REACT_FORWARD_REF_TYPE;
}
function isFragment(object) {
  return typeOf(object) === REACT_FRAGMENT_TYPE;
}
function isLazy(object) {
  return typeOf(object) === REACT_LAZY_TYPE;
}
function isMemo(object) {
  return typeOf(object) === REACT_MEMO_TYPE;
}
function isPortal(object) {
  return typeOf(object) === REACT_PORTAL_TYPE;
}
function isProfiler(object) {
  return typeOf(object) === REACT_PROFILER_TYPE;
}
function isStrictMode(object) {
  return typeOf(object) === REACT_STRICT_MODE_TYPE;
}
function isSuspense(object) {
  return typeOf(object) === REACT_SUSPENSE_TYPE;
}

exports.typeOf = typeOf;
exports.AsyncMode = AsyncMode;
exports.ConcurrentMode = ConcurrentMode;
exports.ContextConsumer = ContextConsumer;
exports.ContextProvider = ContextProvider;
exports.Element = Element;
exports.ForwardRef = ForwardRef;
exports.Fragment = Fragment;
exports.Lazy = Lazy;
exports.Memo = Memo;
exports.Portal = Portal;
exports.Profiler = Profiler;
exports.StrictMode = StrictMode;
exports.Suspense = Suspense;
exports.isValidElementType = isValidElementType;
exports.isAsyncMode = isAsyncMode;
exports.isConcurrentMode = isConcurrentMode;
exports.isContextConsumer = isContextConsumer;
exports.isContextProvider = isContextProvider;
exports.isElement = isElement;
exports.isForwardRef = isForwardRef;
exports.isFragment = isFragment;
exports.isLazy = isLazy;
exports.isMemo = isMemo;
exports.isPortal = isPortal;
exports.isProfiler = isProfiler;
exports.isStrictMode = isStrictMode;
exports.isSuspense = isSuspense;
  })();
}
});

var reactIs = createCommonjsModule(function (module) {

if (process.env.NODE_ENV === 'production') {
  module.exports = reactIs_production_min;
} else {
  module.exports = reactIs_development;
}
});

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/
/* eslint-disable no-unused-vars */
var getOwnPropertySymbols = Object.getOwnPropertySymbols;
var hasOwnProperty = Object.prototype.hasOwnProperty;
var propIsEnumerable = Object.prototype.propertyIsEnumerable;

function toObject(val) {
	if (val === null || val === undefined) {
		throw new TypeError('Object.assign cannot be called with null or undefined');
	}

	return Object(val);
}

function shouldUseNative() {
	try {
		if (!Object.assign) {
			return false;
		}

		// Detect buggy property enumeration order in older V8 versions.

		// https://bugs.chromium.org/p/v8/issues/detail?id=4118
		var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
		test1[5] = 'de';
		if (Object.getOwnPropertyNames(test1)[0] === '5') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test2 = {};
		for (var i = 0; i < 10; i++) {
			test2['_' + String.fromCharCode(i)] = i;
		}
		var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
			return test2[n];
		});
		if (order2.join('') !== '0123456789') {
			return false;
		}

		// https://bugs.chromium.org/p/v8/issues/detail?id=3056
		var test3 = {};
		'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
			test3[letter] = letter;
		});
		if (Object.keys(Object.assign({}, test3)).join('') !==
				'abcdefghijklmnopqrst') {
			return false;
		}

		return true;
	} catch (err) {
		// We don't expect any of the above to throw, but better to be safe.
		return false;
	}
}

var objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
	var from;
	var to = toObject(target);
	var symbols;

	for (var s = 1; s < arguments.length; s++) {
		from = Object(arguments[s]);

		for (var key in from) {
			if (hasOwnProperty.call(from, key)) {
				to[key] = from[key];
			}
		}

		if (getOwnPropertySymbols) {
			symbols = getOwnPropertySymbols(from);
			for (var i = 0; i < symbols.length; i++) {
				if (propIsEnumerable.call(from, symbols[i])) {
					to[symbols[i]] = from[symbols[i]];
				}
			}
		}
	}

	return to;
};

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

var ReactPropTypesSecret_1 = ReactPropTypesSecret;

var printWarning = function() {};

if (process.env.NODE_ENV !== 'production') {
  var ReactPropTypesSecret$1 = ReactPropTypesSecret_1;
  var loggedTypeFailures = {};
  var has = Function.call.bind(Object.prototype.hasOwnProperty);

  printWarning = function(text) {
    var message = 'Warning: ' + text;
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
}

/**
 * Assert that the values match with the type specs.
 * Error messages are memorized and will only be shown once.
 *
 * @param {object} typeSpecs Map of name to a ReactPropType
 * @param {object} values Runtime values that need to be type-checked
 * @param {string} location e.g. "prop", "context", "child context"
 * @param {string} componentName Name of the component for error messages.
 * @param {?Function} getStack Returns the component stack.
 * @private
 */
function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
  if (process.env.NODE_ENV !== 'production') {
    for (var typeSpecName in typeSpecs) {
      if (has(typeSpecs, typeSpecName)) {
        var error;
        // Prop type validation may throw. In case they do, we don't want to
        // fail the render phase where it didn't fail before. So we log it.
        // After these have been cleaned up, we'll let them throw.
        try {
          // This is intentionally an invariant that gets caught. It's the same
          // behavior as without this statement except with a better message.
          if (typeof typeSpecs[typeSpecName] !== 'function') {
            var err = Error(
              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.'
            );
            err.name = 'Invariant Violation';
            throw err;
          }
          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret$1);
        } catch (ex) {
          error = ex;
        }
        if (error && !(error instanceof Error)) {
          printWarning(
            (componentName || 'React class') + ': type specification of ' +
            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
            'You may have forgotten to pass an argument to the type checker ' +
            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
            'shape all require an argument).'
          );
        }
        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
          // Only monitor this failure once because there tends to be a lot of the
          // same error.
          loggedTypeFailures[error.message] = true;

          var stack = getStack ? getStack() : '';

          printWarning(
            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
          );
        }
      }
    }
  }
}

/**
 * Resets warning cache when testing.
 *
 * @private
 */
checkPropTypes.resetWarningCache = function() {
  if (process.env.NODE_ENV !== 'production') {
    loggedTypeFailures = {};
  }
};

var checkPropTypes_1 = checkPropTypes;

var has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
var printWarning$1 = function() {};

if (process.env.NODE_ENV !== 'production') {
  printWarning$1 = function(text) {
    var message = 'Warning: ' + text;
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
}

function emptyFunctionThatReturnsNull() {
  return null;
}

var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
  /* global Symbol */
  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

  /**
   * Returns the iterator method function contained on the iterable object.
   *
   * Be sure to invoke the function with the iterable as context:
   *
   *     var iteratorFn = getIteratorFn(myIterable);
   *     if (iteratorFn) {
   *       var iterator = iteratorFn.call(myIterable);
   *       ...
   *     }
   *
   * @param {?object} maybeIterable
   * @return {?function}
   */
  function getIteratorFn(maybeIterable) {
    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
    if (typeof iteratorFn === 'function') {
      return iteratorFn;
    }
  }

  /**
   * Collection of methods that allow declaration and validation of props that are
   * supplied to React components. Example usage:
   *
   *   var Props = require('ReactPropTypes');
   *   var MyArticle = React.createClass({
   *     propTypes: {
   *       // An optional string prop named "description".
   *       description: Props.string,
   *
   *       // A required enum prop named "category".
   *       category: Props.oneOf(['News','Photos']).isRequired,
   *
   *       // A prop named "dialog" that requires an instance of Dialog.
   *       dialog: Props.instanceOf(Dialog).isRequired
   *     },
   *     render: function() { ... }
   *   });
   *
   * A more formal specification of how these methods are used:
   *
   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
   *   decl := ReactPropTypes.{type}(.isRequired)?
   *
   * Each and every declaration produces a function with the same signature. This
   * allows the creation of custom validation functions. For example:
   *
   *  var MyLink = React.createClass({
   *    propTypes: {
   *      // An optional string or URI prop named "href".
   *      href: function(props, propName, componentName) {
   *        var propValue = props[propName];
   *        if (propValue != null && typeof propValue !== 'string' &&
   *            !(propValue instanceof URI)) {
   *          return new Error(
   *            'Expected a string or an URI for ' + propName + ' in ' +
   *            componentName
   *          );
   *        }
   *      }
   *    },
   *    render: function() {...}
   *  });
   *
   * @internal
   */

  var ANONYMOUS = '<<anonymous>>';

  // Important!
  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
  var ReactPropTypes = {
    array: createPrimitiveTypeChecker('array'),
    bool: createPrimitiveTypeChecker('boolean'),
    func: createPrimitiveTypeChecker('function'),
    number: createPrimitiveTypeChecker('number'),
    object: createPrimitiveTypeChecker('object'),
    string: createPrimitiveTypeChecker('string'),
    symbol: createPrimitiveTypeChecker('symbol'),

    any: createAnyTypeChecker(),
    arrayOf: createArrayOfTypeChecker,
    element: createElementTypeChecker(),
    elementType: createElementTypeTypeChecker(),
    instanceOf: createInstanceTypeChecker,
    node: createNodeChecker(),
    objectOf: createObjectOfTypeChecker,
    oneOf: createEnumTypeChecker,
    oneOfType: createUnionTypeChecker,
    shape: createShapeTypeChecker,
    exact: createStrictShapeTypeChecker,
  };

  /**
   * inlined Object.is polyfill to avoid requiring consumers ship their own
   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
   */
  /*eslint-disable no-self-compare*/
  function is(x, y) {
    // SameValue algorithm
    if (x === y) {
      // Steps 1-5, 7-10
      // Steps 6.b-6.e: +0 != -0
      return x !== 0 || 1 / x === 1 / y;
    } else {
      // Step 6.a: NaN == NaN
      return x !== x && y !== y;
    }
  }
  /*eslint-enable no-self-compare*/

  /**
   * We use an Error-like object for backward compatibility as people may call
   * PropTypes directly and inspect their output. However, we don't use real
   * Errors anymore. We don't inspect their stack anyway, and creating them
   * is prohibitively expensive if they are created too often, such as what
   * happens in oneOfType() for any type before the one that matched.
   */
  function PropTypeError(message) {
    this.message = message;
    this.stack = '';
  }
  // Make `instanceof Error` still work for returned errors.
  PropTypeError.prototype = Error.prototype;

  function createChainableTypeChecker(validate) {
    if (process.env.NODE_ENV !== 'production') {
      var manualPropTypeCallCache = {};
      var manualPropTypeWarningCount = 0;
    }
    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
      componentName = componentName || ANONYMOUS;
      propFullName = propFullName || propName;

      if (secret !== ReactPropTypesSecret_1) {
        if (throwOnDirectAccess) {
          // New behavior only for users of `prop-types` package
          var err = new Error(
            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
            'Use `PropTypes.checkPropTypes()` to call them. ' +
            'Read more at http://fb.me/use-check-prop-types'
          );
          err.name = 'Invariant Violation';
          throw err;
        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
          // Old behavior for people using React.PropTypes
          var cacheKey = componentName + ':' + propName;
          if (
            !manualPropTypeCallCache[cacheKey] &&
            // Avoid spamming the console because they are often not actionable except for lib authors
            manualPropTypeWarningCount < 3
          ) {
            printWarning$1(
              'You are manually calling a React.PropTypes validation ' +
              'function for the `' + propFullName + '` prop on `' + componentName  + '`. This is deprecated ' +
              'and will throw in the standalone `prop-types` package. ' +
              'You may be seeing this warning due to a third-party PropTypes ' +
              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
            );
            manualPropTypeCallCache[cacheKey] = true;
            manualPropTypeWarningCount++;
          }
        }
      }
      if (props[propName] == null) {
        if (isRequired) {
          if (props[propName] === null) {
            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
          }
          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
        }
        return null;
      } else {
        return validate(props, propName, componentName, location, propFullName);
      }
    }

    var chainedCheckType = checkType.bind(null, false);
    chainedCheckType.isRequired = checkType.bind(null, true);

    return chainedCheckType;
  }

  function createPrimitiveTypeChecker(expectedType) {
    function validate(props, propName, componentName, location, propFullName, secret) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== expectedType) {
        // `propValue` being instance of, say, date/regexp, pass the 'object'
        // check, but we can offer a more precise error message here rather than
        // 'of type `object`'.
        var preciseType = getPreciseType(propValue);

        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createAnyTypeChecker() {
    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
  }

  function createArrayOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
      }
      var propValue = props[propName];
      if (!Array.isArray(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
      }
      for (var i = 0; i < propValue.length; i++) {
        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret_1);
        if (error instanceof Error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!isValidElement(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createElementTypeTypeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      if (!reactIs.isValidElementType(propValue)) {
        var propType = getPropType(propValue);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createInstanceTypeChecker(expectedClass) {
    function validate(props, propName, componentName, location, propFullName) {
      if (!(props[propName] instanceof expectedClass)) {
        var expectedClassName = expectedClass.name || ANONYMOUS;
        var actualClassName = getClassName(props[propName]);
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createEnumTypeChecker(expectedValues) {
    if (!Array.isArray(expectedValues)) {
      if (process.env.NODE_ENV !== 'production') {
        if (arguments.length > 1) {
          printWarning$1(
            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
          );
        } else {
          printWarning$1('Invalid argument supplied to oneOf, expected an array.');
        }
      }
      return emptyFunctionThatReturnsNull;
    }

    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      for (var i = 0; i < expectedValues.length; i++) {
        if (is(propValue, expectedValues[i])) {
          return null;
        }
      }

      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
        var type = getPreciseType(value);
        if (type === 'symbol') {
          return String(value);
        }
        return value;
      });
      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createObjectOfTypeChecker(typeChecker) {
    function validate(props, propName, componentName, location, propFullName) {
      if (typeof typeChecker !== 'function') {
        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
      }
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
      }
      for (var key in propValue) {
        if (has$1(propValue, key)) {
          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
          if (error instanceof Error) {
            return error;
          }
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createUnionTypeChecker(arrayOfTypeCheckers) {
    if (!Array.isArray(arrayOfTypeCheckers)) {
      process.env.NODE_ENV !== 'production' ? printWarning$1('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
      return emptyFunctionThatReturnsNull;
    }

    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
      var checker = arrayOfTypeCheckers[i];
      if (typeof checker !== 'function') {
        printWarning$1(
          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
        );
        return emptyFunctionThatReturnsNull;
      }
    }

    function validate(props, propName, componentName, location, propFullName) {
      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i];
        if (checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret_1) == null) {
          return null;
        }
      }

      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`.'));
    }
    return createChainableTypeChecker(validate);
  }

  function createNodeChecker() {
    function validate(props, propName, componentName, location, propFullName) {
      if (!isNode(props[propName])) {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      for (var key in shapeTypes) {
        var checker = shapeTypes[key];
        if (!checker) {
          continue;
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }
    return createChainableTypeChecker(validate);
  }

  function createStrictShapeTypeChecker(shapeTypes) {
    function validate(props, propName, componentName, location, propFullName) {
      var propValue = props[propName];
      var propType = getPropType(propValue);
      if (propType !== 'object') {
        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
      }
      // We need to check all keys in case some are required but missing from
      // props.
      var allKeys = objectAssign({}, props[propName], shapeTypes);
      for (var key in allKeys) {
        var checker = shapeTypes[key];
        if (!checker) {
          return new PropTypeError(
            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
            '\nValid keys: ' +  JSON.stringify(Object.keys(shapeTypes), null, '  ')
          );
        }
        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret_1);
        if (error) {
          return error;
        }
      }
      return null;
    }

    return createChainableTypeChecker(validate);
  }

  function isNode(propValue) {
    switch (typeof propValue) {
      case 'number':
      case 'string':
      case 'undefined':
        return true;
      case 'boolean':
        return !propValue;
      case 'object':
        if (Array.isArray(propValue)) {
          return propValue.every(isNode);
        }
        if (propValue === null || isValidElement(propValue)) {
          return true;
        }

        var iteratorFn = getIteratorFn(propValue);
        if (iteratorFn) {
          var iterator = iteratorFn.call(propValue);
          var step;
          if (iteratorFn !== propValue.entries) {
            while (!(step = iterator.next()).done) {
              if (!isNode(step.value)) {
                return false;
              }
            }
          } else {
            // Iterator will provide entry [k,v] tuples rather than values.
            while (!(step = iterator.next()).done) {
              var entry = step.value;
              if (entry) {
                if (!isNode(entry[1])) {
                  return false;
                }
              }
            }
          }
        } else {
          return false;
        }

        return true;
      default:
        return false;
    }
  }

  function isSymbol(propType, propValue) {
    // Native Symbol.
    if (propType === 'symbol') {
      return true;
    }

    // falsy value can't be a Symbol
    if (!propValue) {
      return false;
    }

    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
    if (propValue['@@toStringTag'] === 'Symbol') {
      return true;
    }

    // Fallback for non-spec compliant Symbols which are polyfilled.
    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
      return true;
    }

    return false;
  }

  // Equivalent of `typeof` but with special handling for array and regexp.
  function getPropType(propValue) {
    var propType = typeof propValue;
    if (Array.isArray(propValue)) {
      return 'array';
    }
    if (propValue instanceof RegExp) {
      // Old webkits (at least until Android 4.0) return 'function' rather than
      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
      // passes PropTypes.object.
      return 'object';
    }
    if (isSymbol(propType, propValue)) {
      return 'symbol';
    }
    return propType;
  }

  // This handles more types than `getPropType`. Only used for error messages.
  // See `createPrimitiveTypeChecker`.
  function getPreciseType(propValue) {
    if (typeof propValue === 'undefined' || propValue === null) {
      return '' + propValue;
    }
    var propType = getPropType(propValue);
    if (propType === 'object') {
      if (propValue instanceof Date) {
        return 'date';
      } else if (propValue instanceof RegExp) {
        return 'regexp';
      }
    }
    return propType;
  }

  // Returns a string that is postfixed to a warning about an invalid type.
  // For example, "undefined" or "of type array"
  function getPostfixForTypeWarning(value) {
    var type = getPreciseType(value);
    switch (type) {
      case 'array':
      case 'object':
        return 'an ' + type;
      case 'boolean':
      case 'date':
      case 'regexp':
        return 'a ' + type;
      default:
        return type;
    }
  }

  // Returns class name of the object, if any.
  function getClassName(propValue) {
    if (!propValue.constructor || !propValue.constructor.name) {
      return ANONYMOUS;
    }
    return propValue.constructor.name;
  }

  ReactPropTypes.checkPropTypes = checkPropTypes_1;
  ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache;
  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

function emptyFunction() {}
function emptyFunctionWithReset() {}
emptyFunctionWithReset.resetWarningCache = emptyFunction;

var factoryWithThrowingShims = function() {
  function shim(props, propName, componentName, location, propFullName, secret) {
    if (secret === ReactPropTypesSecret_1) {
      // It is still safe when called from React.
      return;
    }
    var err = new Error(
      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
      'Use PropTypes.checkPropTypes() to call them. ' +
      'Read more at http://fb.me/use-check-prop-types'
    );
    err.name = 'Invariant Violation';
    throw err;
  }  shim.isRequired = shim;
  function getShim() {
    return shim;
  }  // Important!
  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
  var ReactPropTypes = {
    array: shim,
    bool: shim,
    func: shim,
    number: shim,
    object: shim,
    string: shim,
    symbol: shim,

    any: shim,
    arrayOf: getShim,
    element: shim,
    elementType: shim,
    instanceOf: getShim,
    node: shim,
    objectOf: getShim,
    oneOf: getShim,
    oneOfType: getShim,
    shape: getShim,
    exact: getShim,

    checkPropTypes: emptyFunctionWithReset,
    resetWarningCache: emptyFunction
  };

  ReactPropTypes.PropTypes = ReactPropTypes;

  return ReactPropTypes;
};

var propTypes = createCommonjsModule(function (module) {
/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = reactIs;

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  module.exports = factoryWithTypeCheckers(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  module.exports = factoryWithThrowingShims();
}
});

/* eslint-disable no-shadow */
/* eslint-disable no-array-constructor */
/* eslint-disable eqeqeq */
var CHAR_TILDE = 126;
var CODE_FNC1 = 102;
var SET_STARTA = 103;
var SET_STARTB = 104;
var SET_STARTC = 105;
var SET_SHIFT = 98;
var SET_CODEA = 101;
var SET_CODEB = 100;
var SET_STOP = 106;
var REPLACE_CODES = {
    CHAR_TILDE: CODE_FNC1 // ~ corresponds to FNC1 in GS1-128 standard
};
var CODESET = {
    ANY: 1,
    AB: 2,
    A: 3,
    B: 4,
    C: 5
};
var PATTERNS = [
    [2, 1, 2, 2, 2, 2, 0, 0],
    [2, 2, 2, 1, 2, 2, 0, 0],
    [2, 2, 2, 2, 2, 1, 0, 0],
    [1, 2, 1, 2, 2, 3, 0, 0],
    [1, 2, 1, 3, 2, 2, 0, 0],
    [1, 3, 1, 2, 2, 2, 0, 0],
    [1, 2, 2, 2, 1, 3, 0, 0],
    [1, 2, 2, 3, 1, 2, 0, 0],
    [1, 3, 2, 2, 1, 2, 0, 0],
    [2, 2, 1, 2, 1, 3, 0, 0],
    [2, 2, 1, 3, 1, 2, 0, 0],
    [2, 3, 1, 2, 1, 2, 0, 0],
    [1, 1, 2, 2, 3, 2, 0, 0],
    [1, 2, 2, 1, 3, 2, 0, 0],
    [1, 2, 2, 2, 3, 1, 0, 0],
    [1, 1, 3, 2, 2, 2, 0, 0],
    [1, 2, 3, 1, 2, 2, 0, 0],
    [1, 2, 3, 2, 2, 1, 0, 0],
    [2, 2, 3, 2, 1, 1, 0, 0],
    [2, 2, 1, 1, 3, 2, 0, 0],
    [2, 2, 1, 2, 3, 1, 0, 0],
    [2, 1, 3, 2, 1, 2, 0, 0],
    [2, 2, 3, 1, 1, 2, 0, 0],
    [3, 1, 2, 1, 3, 1, 0, 0],
    [3, 1, 1, 2, 2, 2, 0, 0],
    [3, 2, 1, 1, 2, 2, 0, 0],
    [3, 2, 1, 2, 2, 1, 0, 0],
    [3, 1, 2, 2, 1, 2, 0, 0],
    [3, 2, 2, 1, 1, 2, 0, 0],
    [3, 2, 2, 2, 1, 1, 0, 0],
    [2, 1, 2, 1, 2, 3, 0, 0],
    [2, 1, 2, 3, 2, 1, 0, 0],
    [2, 3, 2, 1, 2, 1, 0, 0],
    [1, 1, 1, 3, 2, 3, 0, 0],
    [1, 3, 1, 1, 2, 3, 0, 0],
    [1, 3, 1, 3, 2, 1, 0, 0],
    [1, 1, 2, 3, 1, 3, 0, 0],
    [1, 3, 2, 1, 1, 3, 0, 0],
    [1, 3, 2, 3, 1, 1, 0, 0],
    [2, 1, 1, 3, 1, 3, 0, 0],
    [2, 3, 1, 1, 1, 3, 0, 0],
    [2, 3, 1, 3, 1, 1, 0, 0],
    [1, 1, 2, 1, 3, 3, 0, 0],
    [1, 1, 2, 3, 3, 1, 0, 0],
    [1, 3, 2, 1, 3, 1, 0, 0],
    [1, 1, 3, 1, 2, 3, 0, 0],
    [1, 1, 3, 3, 2, 1, 0, 0],
    [1, 3, 3, 1, 2, 1, 0, 0],
    [3, 1, 3, 1, 2, 1, 0, 0],
    [2, 1, 1, 3, 3, 1, 0, 0],
    [2, 3, 1, 1, 3, 1, 0, 0],
    [2, 1, 3, 1, 1, 3, 0, 0],
    [2, 1, 3, 3, 1, 1, 0, 0],
    [2, 1, 3, 1, 3, 1, 0, 0],
    [3, 1, 1, 1, 2, 3, 0, 0],
    [3, 1, 1, 3, 2, 1, 0, 0],
    [3, 3, 1, 1, 2, 1, 0, 0],
    [3, 1, 2, 1, 1, 3, 0, 0],
    [3, 1, 2, 3, 1, 1, 0, 0],
    [3, 3, 2, 1, 1, 1, 0, 0],
    [3, 1, 4, 1, 1, 1, 0, 0],
    [2, 2, 1, 4, 1, 1, 0, 0],
    [4, 3, 1, 1, 1, 1, 0, 0],
    [1, 1, 1, 2, 2, 4, 0, 0],
    [1, 1, 1, 4, 2, 2, 0, 0],
    [1, 2, 1, 1, 2, 4, 0, 0],
    [1, 2, 1, 4, 2, 1, 0, 0],
    [1, 4, 1, 1, 2, 2, 0, 0],
    [1, 4, 1, 2, 2, 1, 0, 0],
    [1, 1, 2, 2, 1, 4, 0, 0],
    [1, 1, 2, 4, 1, 2, 0, 0],
    [1, 2, 2, 1, 1, 4, 0, 0],
    [1, 2, 2, 4, 1, 1, 0, 0],
    [1, 4, 2, 1, 1, 2, 0, 0],
    [1, 4, 2, 2, 1, 1, 0, 0],
    [2, 4, 1, 2, 1, 1, 0, 0],
    [2, 2, 1, 1, 1, 4, 0, 0],
    [4, 1, 3, 1, 1, 1, 0, 0],
    [2, 4, 1, 1, 1, 2, 0, 0],
    [1, 3, 4, 1, 1, 1, 0, 0],
    [1, 1, 1, 2, 4, 2, 0, 0],
    [1, 2, 1, 1, 4, 2, 0, 0],
    [1, 2, 1, 2, 4, 1, 0, 0],
    [1, 1, 4, 2, 1, 2, 0, 0],
    [1, 2, 4, 1, 1, 2, 0, 0],
    [1, 2, 4, 2, 1, 1, 0, 0],
    [4, 1, 1, 2, 1, 2, 0, 0],
    [4, 2, 1, 1, 1, 2, 0, 0],
    [4, 2, 1, 2, 1, 1, 0, 0],
    [2, 1, 2, 1, 4, 1, 0, 0],
    [2, 1, 4, 1, 2, 1, 0, 0],
    [4, 1, 2, 1, 2, 1, 0, 0],
    [1, 1, 1, 1, 4, 3, 0, 0],
    [1, 1, 1, 3, 4, 1, 0, 0],
    [1, 3, 1, 1, 4, 1, 0, 0],
    [1, 1, 4, 1, 1, 3, 0, 0],
    [1, 1, 4, 3, 1, 1, 0, 0],
    [4, 1, 1, 1, 1, 3, 0, 0],
    [4, 1, 1, 3, 1, 1, 0, 0],
    [1, 1, 3, 1, 4, 1, 0, 0],
    [1, 1, 4, 1, 3, 1, 0, 0],
    [3, 1, 1, 1, 4, 1, 0, 0],
    [4, 1, 1, 1, 3, 1, 0, 0],
    [2, 1, 1, 4, 1, 2, 0, 0],
    [2, 1, 1, 2, 1, 4, 0, 0],
    [2, 1, 1, 2, 3, 2, 0, 0],
    [2, 3, 3, 1, 1, 1, 2, 0] // 106
];
function getBytes(str) {
    var bytes = [];
    for (var i = 0; i < str.length; i++) {
        bytes.push(str.charCodeAt(i));
    }
    return bytes;
}
function code128(text) {
    var codes = stringToCode128(text);
    var buffer = [];
    for (var i = 0; i < codes.length; i++) {
        var c = codes[i];
        for (var bar = 0; bar < 8; bar += 2) {
            var barLen = PATTERNS[c][bar];
            buffer = buffer.concat(Array(barLen).fill(1));
            var spcLen = PATTERNS[c][bar + 1];
            buffer = buffer.concat(Array(spcLen).fill(0));
        }
    }
    return buffer;
}
function stringToCode128(text) {
    var barc = {
        currcs: CODESET.C
    };
    var bytes = getBytes(text);
    // decide starting codeset
    var index = bytes[0] == CHAR_TILDE ? 1 : 0;
    var csa1 = bytes.length > 0 ? codeSetAllowedFor(bytes[index++]) : CODESET.AB;
    var csa2 = bytes.length > 0 ? codeSetAllowedFor(bytes[index++]) : CODESET.AB;
    barc.currcs = getBestStartSet(csa1, csa2);
    barc.currcs = perhapsCodeC(bytes, barc.currcs);
    // if no codeset changes this will end up with bytes.length+3
    // start, checksum and stop
    var codes = [];
    switch (barc.currcs) {
        case CODESET.A:
            codes.push(SET_STARTA);
            break;
        case CODESET.B:
            codes.push(SET_STARTB);
            break;
        default:
            codes.push(SET_STARTC);
            break;
    }
    for (var i = 0; i < bytes.length; i++) {
        var b1 = bytes[i]; // get the first of a pair
        // should we translate/replace
        if (b1 in REPLACE_CODES) {
            codes.push(REPLACE_CODES[b1]);
            i++; // jump to next
            b1 = bytes[i];
        }
        // get the next in the pair if possible
        var b2 = bytes.length > i + 1 ? bytes[i + 1] : -1;
        codes = codes.concat(codesForChar(b1, b2, barc.currcs));
        // code C takes 2 chars each time
        if (barc.currcs == CODESET.C)
            i++;
    }
    // calculate checksum according to Code 128 standards
    var checksum = codes[0];
    for (var weight = 1; weight < codes.length; weight++) {
        checksum += weight * codes[weight];
    }
    codes.push(checksum % 103);
    codes.push(SET_STOP);
    // encoding should now be complete
    return codes;
    function getBestStartSet(csa1, csa2) {
        // tries to figure out the best codeset
        // to start with to get the most compact code
        var vote = 0;
        vote += csa1 == CODESET.A ? 1 : 0;
        vote += csa1 == CODESET.B ? -1 : 0;
        vote += csa2 == CODESET.A ? 1 : 0;
        vote += csa2 == CODESET.B ? -1 : 0;
        // tie goes to B due to my own predudices
        return vote > 0 ? CODESET.A : CODESET.B;
    }
    function perhapsCodeC(bytes, codeset) {
        for (var i = 0; i < bytes.length; i++) {
            var b = bytes[i];
            if ((b < 48 || b > 57) && b != CHAR_TILDE)
                return codeset;
        }
        return CODESET.C;
    }
    // chr1 is current byte
    // chr2 is the next byte to process. looks ahead.
    function codesForChar(chr1, chr2, currcs) {
        var result = [];
        var shifter = -1;
        if (charCompatible(chr1, currcs)) {
            if (currcs == CODESET.C) {
                if (chr2 == -1) {
                    shifter = SET_CODEB;
                    currcs = CODESET.B;
                }
                else if (chr2 != -1 && !charCompatible(chr2, currcs)) {
                    // need to check ahead as well
                    if (charCompatible(chr2, CODESET.A)) {
                        shifter = SET_CODEA;
                        currcs = CODESET.A;
                    }
                    else {
                        shifter = SET_CODEB;
                        currcs = CODESET.B;
                    }
                }
            }
        }
        else {
            // if there is a next char AND that next char is also not compatible
            if (chr2 != -1 && !charCompatible(chr2, currcs)) {
                // need to switch code sets
                switch (currcs) {
                    case CODESET.A:
                        shifter = SET_CODEB;
                        currcs = CODESET.B;
                        break;
                    case CODESET.B:
                        shifter = SET_CODEA;
                        currcs = CODESET.A;
                        break;
                }
            }
            else {
                // no need to shift code sets, a temporary SHIFT will suffice
                shifter = SET_SHIFT;
            }
        }
        // ok some type of shift is nessecary
        if (shifter != -1) {
            result.push(shifter);
            result.push(codeValue(chr1));
        }
        else {
            if (currcs == CODESET.C) {
                // include next as well
                result.push(codeValue(chr1, chr2));
            }
            else {
                result.push(codeValue(chr1));
            }
        }
        barc.currcs = currcs;
        return result;
    }
}
// reduce the ascii code to fit into the Code128 char table
function codeValue(chr1, chr2) {
    if (chr2 === void 0) { chr2 = undefined; }
    if (typeof chr2 === 'undefined') {
        return chr1 >= 32 ? chr1 - 32 : chr1 + 64;
    }
    else {
        return parseInt(String.fromCharCode(chr1) + String.fromCharCode(chr2));
    }
}
function charCompatible(chr, codeset) {
    var csa = codeSetAllowedFor(chr);
    if (csa == CODESET.ANY)
        return true;
    // if we need to change from current
    if (csa == CODESET.AB)
        return true;
    if (csa == CODESET.A && codeset == CODESET.A)
        return true;
    if (csa == CODESET.B && codeset == CODESET.B)
        return true;
    return false;
}
function codeSetAllowedFor(chr) {
    if (chr >= 48 && chr <= 57) {
        // 0-9
        return CODESET.ANY;
    }
    else if (chr >= 32 && chr <= 95) {
        // 0-9 A-Z
        return CODESET.AB;
    }
    else {
        // if non printable
        return chr < 32 ? CODESET.A : CODESET.B;
    }
}

function getLittleEndianHex(value) {
    var result = [];
    for (var bytes = 4; bytes > 0; bytes--) {
        result.push(String.fromCharCode(value & 255));
        value >>= 8;
    }
    return result.join('');
}
function btoa(string) {
    var b64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=';
    string = String(string);
    var bitmap;
    var a;
    var b;
    var c;
    var result = '';
    var i = 0;
    var rest = string.length % 3; // To determine the final padding
    // eslint-disable-next-line space-in-parens
    for (; i < string.length;) {
        if ((a = string.charCodeAt(i++)) > 255 ||
            (b = string.charCodeAt(i++)) > 255 ||
            (c = string.charCodeAt(i++)) > 255) {
            throw new TypeError("Failed to execute 'btoa' on 'Window': The string to be encoded contains characters outside of the Latin1 range.");
        }
        bitmap = (a << 16) | (b << 8) | c;
        result +=
            b64.charAt((bitmap >> 18) & 63) +
                b64.charAt((bitmap >> 12) & 63) +
                b64.charAt((bitmap >> 6) & 63) +
                b64.charAt(bitmap & 63);
    }
    // If there's need of padding, replace the last 'A's with equal signs
    return rest ? result.slice(0, rest - 3) + '==='.substring(rest) : result;
}
function getBuffer(_a) {
    var pieces = _a.pieces, width = _a.width, extraBytes = _a.extraBytes, _b = _a.scale, scale = _b === void 0 ? 1 : _b;
    return pieces
        .map(function (piece) { return Array(scale).fill(piece); })
        .reduce(function (acc, x) { return acc.concat(x); }, [])
        .map(function (piece, index) {
        var code = parseInt(piece) ? 0 : 255;
        var colors = [code, code, code];
        if (!((index % width) - 1) && extraBytes) {
            return colors.concat(Array(extraBytes).fill(0));
        }
        else {
            return colors;
        }
    })
        .reduce(function (acc, x) { return acc.concat(x); }, [])
        .map(function (x) { return String.fromCharCode(x); })
        .join('');
}
function barcode(_a) {
    var text = _a.text, _b = _a.scale, scale = _b === void 0 ? 4 : _b;
    if (text) {
        var pieces = code128(text);
        var width = pieces.length * scale;
        var height = 1;
        var extraBytes = width % 4;
        var colorSize = height * (3 * width + extraBytes);
        var offset = 54;
        var fileSize = colorSize + offset;
        var fileSizeBytes = getLittleEndianHex(fileSize);
        var numFileBytes = getLittleEndianHex(colorSize);
        var w = getLittleEndianHex(width);
        var h = getLittleEndianHex(height);
        var imgdata = getBuffer({ pieces: pieces, width: width, extraBytes: extraBytes, scale: scale });
        var header = 'BM' + // Signature
            fileSizeBytes + // size of the file (bytes)
            '\x00\x00' + // reserved
            '\x00\x00' + // reserved
            '\x36\x00\x00\x00' + // offset of where BMP data lives (54 bytes)
            '\x28\x00\x00\x00' + // number of remaining bytes in header from here (40 bytes)
            w + // the width of the bitmap in pixels*
            h + // the height of the bitmap in pixels*
            '\x01\x00' + // the number of color planes (1)
            '\x18\x00' + // 24 bits / pixel
            '\x00\x00\x00\x00' + // No compression (0)
            numFileBytes + // size of the BMP data (bytes)*
            '\x13\x0B\x00\x00' + // 2835 pixels/meter - horizontal resolution
            '\x13\x0B\x00\x00' + // 2835 pixels/meter - the vertical resolution
            '\x00\x00\x00\x00' + // Number of colors in the palette (keep 0 for 32-bit)
            '\x00\x00\x00\x00'; // 0 important colors (means all colors are important)
        return 'data:image/bmp;base64,' + btoa(header + imgdata);
    }
}

var Barcode = function (_a) {
    var _b = _a.text, text = _b === void 0 ? '' : _b, _c = _a.scale, scale = _c === void 0 ? 4 : _c, _d = _a.width, width = _d === void 0 ? 300 : _d, _e = _a.height, height = _e === void 0 ? 60 : _e, _f = _a.style, style = _f === void 0 ? {} : _f;
    var image = useMemo(function () { return barcode({ text: text, scale: scale }); }, [text, scale]);
    var widthString = width ? width + 'px' : '';
    var heightString = height ? height + 'px' : '';
    var finalStyle = __assign({ width: widthString, height: heightString }, style);
    return React.createElement(Image, { style: finalStyle, src: image || '' });
};
Barcode.propTypes = {
    text: propTypes.string.isRequired,
    scale: propTypes.number,
    width: propTypes.number,
    height: propTypes.number,
    style: propTypes.object,
};

/* eslint-disable no-shadow */
/* eslint-disable no-redeclare */
/* eslint-disable eqeqeq */
/* eslint-disable no-array-constructor */
// ---------------------------------------------------------------------
//
// QR Code Generator for JavaScript
//
// Copyright (c) 2009 Kazuhiko Arase
//
// URL: http://www.d-project.com/
//
// Licensed under the MIT license:
// http://www.opensource.org/licenses/mit-license.php
//
// The word 'QR Code' is registered trademark of
// DENSO WAVE INCORPORATED
// http://www.denso-wave.com/qrcode/faqpatent-e.html
//
// ---------------------------------------------------------------------
/**
 * qrcode
 * @param typeNumber 1 to 40
 * @param errorCorrectLevel 'L','M','Q','H'
 */
var qrcode = function (typeNumber, errorCorrectLevel) {
    var PAD0 = 0xec;
    var PAD1 = 0x11;
    var _typeNumber = typeNumber;
    var _errorCorrectLevel = QRErrorCorrectLevel[errorCorrectLevel];
    var _modules = null;
    var _moduleCount = 0;
    var _dataCache = null;
    var _dataList = [];
    var _this = {};
    var makeImpl = function (test, maskPattern) {
        _moduleCount = _typeNumber * 4 + 17;
        _modules = (function (moduleCount) {
            var modules = new Array(moduleCount);
            for (var row = 0; row < moduleCount; row += 1) {
                modules[row] = new Array(moduleCount);
                for (var col = 0; col < moduleCount; col += 1) {
                    modules[row][col] = null;
                }
            }
            return modules;
        })(_moduleCount);
        setupPositionProbePattern(0, 0);
        setupPositionProbePattern(_moduleCount - 7, 0);
        setupPositionProbePattern(0, _moduleCount - 7);
        setupPositionAdjustPattern();
        setupTimingPattern();
        setupTypeInfo(test, maskPattern);
        if (_typeNumber >= 7) {
            setupTypeNumber(test);
        }
        if (_dataCache == null) {
            _dataCache = createData(_typeNumber, _errorCorrectLevel, _dataList);
        }
        mapData(_dataCache, maskPattern);
    };
    var setupPositionProbePattern = function (row, col) {
        for (var r = -1; r <= 7; r += 1) {
            if (row + r <= -1 || _moduleCount <= row + r)
                continue;
            for (var c = -1; c <= 7; c += 1) {
                if (col + c <= -1 || _moduleCount <= col + c)
                    continue;
                if ((r >= 0 && r <= 6 && (c == 0 || c == 6)) ||
                    (c >= 0 && c <= 6 && (r == 0 || r == 6)) ||
                    (r >= 2 && r <= 4 && c >= 2 && c <= 4)) {
                    _modules[row + r][col + c] = true;
                }
                else {
                    _modules[row + r][col + c] = false;
                }
            }
        }
    };
    var getBestMaskPattern = function () {
        var minLostPoint = 0;
        var pattern = 0;
        for (var i = 0; i < 8; i += 1) {
            makeImpl(true, i);
            var lostPoint = QRUtil.getLostPoint(_this);
            if (i == 0 || minLostPoint > lostPoint) {
                minLostPoint = lostPoint;
                pattern = i;
            }
        }
        return pattern;
    };
    var setupTimingPattern = function () {
        for (var r = 8; r < _moduleCount - 8; r += 1) {
            if (_modules[r][6] != null) {
                continue;
            }
            _modules[r][6] = r % 2 == 0;
        }
        for (var c = 8; c < _moduleCount - 8; c += 1) {
            if (_modules[6][c] != null) {
                continue;
            }
            _modules[6][c] = c % 2 == 0;
        }
    };
    var setupPositionAdjustPattern = function () {
        var pos = QRUtil.getPatternPosition(_typeNumber);
        for (var i = 0; i < pos.length; i += 1) {
            for (var j = 0; j < pos.length; j += 1) {
                var row = pos[i];
                var col = pos[j];
                if (_modules[row][col] != null) {
                    continue;
                }
                for (var r = -2; r <= 2; r += 1) {
                    for (var c = -2; c <= 2; c += 1) {
                        if (r == -2 || r == 2 || c == -2 || c == 2 || (r == 0 && c == 0)) {
                            _modules[row + r][col + c] = true;
                        }
                        else {
                            _modules[row + r][col + c] = false;
                        }
                    }
                }
            }
        }
    };
    var setupTypeNumber = function (test) {
        var bits = QRUtil.getBCHTypeNumber(_typeNumber);
        for (var i = 0; i < 18; i += 1) {
            var mod = !test && ((bits >> i) & 1) == 1;
            _modules[Math.floor(i / 3)][(i % 3) + _moduleCount - 8 - 3] = mod;
        }
        for (var i = 0; i < 18; i += 1) {
            var mod = !test && ((bits >> i) & 1) == 1;
            _modules[(i % 3) + _moduleCount - 8 - 3][Math.floor(i / 3)] = mod;
        }
    };
    var setupTypeInfo = function (test, maskPattern) {
        var data = (_errorCorrectLevel << 3) | maskPattern;
        var bits = QRUtil.getBCHTypeInfo(data);
        // vertical
        for (var i = 0; i < 15; i += 1) {
            var mod = !test && ((bits >> i) & 1) == 1;
            if (i < 6) {
                _modules[i][8] = mod;
            }
            else if (i < 8) {
                _modules[i + 1][8] = mod;
            }
            else {
                _modules[_moduleCount - 15 + i][8] = mod;
            }
        }
        // horizontal
        for (var i = 0; i < 15; i += 1) {
            var mod = !test && ((bits >> i) & 1) == 1;
            if (i < 8) {
                _modules[8][_moduleCount - i - 1] = mod;
            }
            else if (i < 9) {
                _modules[8][15 - i - 1 + 1] = mod;
            }
            else {
                _modules[8][15 - i - 1] = mod;
            }
        }
        // fixed module
        _modules[_moduleCount - 8][8] = !test;
    };
    var mapData = function (data, maskPattern) {
        var inc = -1;
        var row = _moduleCount - 1;
        var bitIndex = 7;
        var byteIndex = 0;
        var maskFunc = QRUtil.getMaskFunction(maskPattern);
        for (var col = _moduleCount - 1; col > 0; col -= 2) {
            if (col == 6)
                col -= 1;
            while (true) {
                for (var c = 0; c < 2; c += 1) {
                    if (_modules[row][col - c] == null) {
                        var dark = false;
                        if (byteIndex < data.length) {
                            dark = ((data[byteIndex] >>> bitIndex) & 1) == 1;
                        }
                        var mask = maskFunc(row, col - c);
                        if (mask) {
                            dark = !dark;
                        }
                        _modules[row][col - c] = dark;
                        bitIndex -= 1;
                        if (bitIndex == -1) {
                            byteIndex += 1;
                            bitIndex = 7;
                        }
                    }
                }
                row += inc;
                if (row < 0 || _moduleCount <= row) {
                    row -= inc;
                    inc = -inc;
                    break;
                }
            }
        }
    };
    var createBytes = function (buffer, rsBlocks) {
        var offset = 0;
        var maxDcCount = 0;
        var maxEcCount = 0;
        var dcdata = new Array(rsBlocks.length);
        var ecdata = new Array(rsBlocks.length);
        for (var r = 0; r < rsBlocks.length; r += 1) {
            var dcCount = rsBlocks[r].dataCount;
            var ecCount = rsBlocks[r].totalCount - dcCount;
            maxDcCount = Math.max(maxDcCount, dcCount);
            maxEcCount = Math.max(maxEcCount, ecCount);
            dcdata[r] = new Array(dcCount);
            for (var i = 0; i < dcdata[r].length; i += 1) {
                dcdata[r][i] = 0xff & buffer.getBuffer()[i + offset];
            }
            offset += dcCount;
            var rsPoly = QRUtil.getErrorCorrectPolynomial(ecCount);
            var rawPoly = qrPolynomial(dcdata[r], rsPoly.getLength() - 1);
            var modPoly = rawPoly.mod(rsPoly);
            ecdata[r] = new Array(rsPoly.getLength() - 1);
            for (var i = 0; i < ecdata[r].length; i += 1) {
                var modIndex = i + modPoly.getLength() - ecdata[r].length;
                ecdata[r][i] = modIndex >= 0 ? modPoly.getAt(modIndex) : 0;
            }
        }
        var totalCodeCount = 0;
        for (var i = 0; i < rsBlocks.length; i += 1) {
            totalCodeCount += rsBlocks[i].totalCount;
        }
        var data = new Array(totalCodeCount);
        var index = 0;
        for (var i = 0; i < maxDcCount; i += 1) {
            for (var r = 0; r < rsBlocks.length; r += 1) {
                if (i < dcdata[r].length) {
                    data[index] = dcdata[r][i];
                    index += 1;
                }
            }
        }
        for (var i = 0; i < maxEcCount; i += 1) {
            for (var r = 0; r < rsBlocks.length; r += 1) {
                if (i < ecdata[r].length) {
                    data[index] = ecdata[r][i];
                    index += 1;
                }
            }
        }
        return data;
    };
    var createData = function (typeNumber, errorCorrectLevel, dataList) {
        var rsBlocks = QRRSBlock.getRSBlocks(typeNumber, errorCorrectLevel);
        var buffer = qrBitBuffer();
        for (var i = 0; i < dataList.length; i += 1) {
            var data = dataList[i];
            buffer.put(data.getMode(), 4);
            buffer.put(data.getLength(), QRUtil.getLengthInBits(data.getMode(), typeNumber));
            data.write(buffer);
        }
        // calc num max data.
        var totalDataCount = 0;
        for (var i = 0; i < rsBlocks.length; i += 1) {
            totalDataCount += rsBlocks[i].dataCount;
        }
        if (buffer.getLengthInBits() > totalDataCount * 8) {
            throw new Error('code length overflow. (' +
                buffer.getLengthInBits() +
                '>' +
                totalDataCount * 8 +
                ')');
        }
        // end code
        if (buffer.getLengthInBits() + 4 <= totalDataCount * 8) {
            buffer.put(0, 4);
        }
        // padding
        while (buffer.getLengthInBits() % 8 != 0) {
            buffer.putBit(false);
        }
        // padding
        while (true) {
            if (buffer.getLengthInBits() >= totalDataCount * 8) {
                break;
            }
            buffer.put(PAD0, 8);
            if (buffer.getLengthInBits() >= totalDataCount * 8) {
                break;
            }
            buffer.put(PAD1, 8);
        }
        return createBytes(buffer, rsBlocks);
    };
    _this.addData = function (data) {
        var newData = qr8BitByte(data);
        _dataList.push(newData);
        _dataCache = null;
    };
    _this.isDark = function (row, col) {
        if (row < 0 || _moduleCount <= row || col < 0 || _moduleCount <= col) {
            throw new Error(row + ',' + col);
        }
        return _modules[row][col];
    };
    _this.getModuleCount = function () {
        return _moduleCount;
    };
    _this.make = function () {
        makeImpl(false, getBestMaskPattern());
    };
    _this.createTableTag = function (cellSize, margin) {
        cellSize = cellSize || 2;
        margin = typeof margin === 'undefined' ? cellSize * 4 : margin;
        var qrHtml = '';
        qrHtml += '<table style="';
        qrHtml += ' border-width: 0px; border-style: none;';
        qrHtml += ' border-collapse: collapse;';
        qrHtml += ' padding: 0px; margin: ' + margin + 'px;';
        qrHtml += '">';
        qrHtml += '<tbody>';
        for (var r = 0; r < _this.getModuleCount(); r += 1) {
            qrHtml += '<tr>';
            for (var c = 0; c < _this.getModuleCount(); c += 1) {
                qrHtml += '<td style="';
                qrHtml += ' border-width: 0px; border-style: none;';
                qrHtml += ' border-collapse: collapse;';
                qrHtml += ' padding: 0px; margin: 0px;';
                qrHtml += ' width: ' + cellSize + 'px;';
                qrHtml += ' height: ' + cellSize + 'px;';
                qrHtml += ' background-color: ';
                qrHtml += _this.isDark(r, c) ? '#000000' : '#ffffff';
                qrHtml += ';';
                qrHtml += '"/>';
            }
            qrHtml += '</tr>';
        }
        qrHtml += '</tbody>';
        qrHtml += '</table>';
        return qrHtml;
    };
    _this.createImgTag = function (cellSize, margin, size) {
        cellSize = cellSize || 2;
        margin = typeof margin === 'undefined' ? cellSize * 4 : margin;
        var min = margin;
        var max = _this.getModuleCount() * cellSize + margin;
        return createImgTag(size, size, function (x, y) {
            if (min <= x && x < max && min <= y && y < max) {
                var c = Math.floor((x - min) / cellSize);
                var r = Math.floor((y - min) / cellSize);
                return _this.isDark(r, c) ? 0 : 1;
            }
            else {
                return 1;
            }
        });
    };
    return _this;
};
// ---------------------------------------------------------------------
// qrcode.stringToBytes
// ---------------------------------------------------------------------
qrcode.stringToBytes = function (s) {
    var bytes = [];
    for (var i = 0; i < s.length; i += 1) {
        var c = s.charCodeAt(i);
        bytes.push(c & 0xff);
    }
    return bytes;
};
// ---------------------------------------------------------------------
// qrcode.createStringToBytes
// ---------------------------------------------------------------------
/**
 * @param unicodeData base64 string of byte array.
 * [16bit Unicode],[16bit Bytes], ...
 * @param numChars
 */
qrcode.createStringToBytes = function (unicodeData, numChars) {
    // create conversion map.
    var unicodeMap = (function () {
        var bin = base64DecodeInputStream(unicodeData);
        var read = function () {
            var b = bin.read();
            if (b == -1)
                throw new Error();
            return b;
        };
        var count = 0;
        var unicodeMap = {};
        while (true) {
            var b0 = bin.read();
            if (b0 == -1)
                break;
            var b1 = read();
            var b2 = read();
            var b3 = read();
            var k = String.fromCharCode((b0 << 8) | b1);
            var v = (b2 << 8) | b3;
            unicodeMap[k] = v;
            count += 1;
        }
        if (count != numChars) {
            throw new Error(count + ' != ' + numChars);
        }
        return unicodeMap;
    })();
    var unknownChar = '?'.charCodeAt(0);
    return function (s) {
        var bytes = [];
        for (var i = 0; i < s.length; i += 1) {
            var c = s.charCodeAt(i);
            if (c < 128) {
                bytes.push(c);
            }
            else {
                var b = unicodeMap[s.charAt(i)];
                if (typeof b === 'number') {
                    if ((b & 0xff) == b) {
                        // 1byte
                        bytes.push(b);
                    }
                    else {
                        // 2bytes
                        bytes.push(b >>> 8);
                        bytes.push(b & 0xff);
                    }
                }
                else {
                    bytes.push(unknownChar);
                }
            }
        }
        return bytes;
    };
};
// ---------------------------------------------------------------------
// QRMode
// ---------------------------------------------------------------------
var QRMode = {
    MODE_NUMBER: 1 << 0,
    MODE_ALPHA_NUM: 1 << 1,
    MODE_8BIT_BYTE: 1 << 2,
    MODE_KANJI: 1 << 3
};
// ---------------------------------------------------------------------
// QRErrorCorrectLevel
// ---------------------------------------------------------------------
var QRErrorCorrectLevel = {
    L: 1,
    M: 0,
    Q: 3,
    H: 2
};
// ---------------------------------------------------------------------
// QRMaskPattern
// ---------------------------------------------------------------------
var QRMaskPattern = {
    PATTERN000: 0,
    PATTERN001: 1,
    PATTERN010: 2,
    PATTERN011: 3,
    PATTERN100: 4,
    PATTERN101: 5,
    PATTERN110: 6,
    PATTERN111: 7
};
// ---------------------------------------------------------------------
// QRUtil
// ---------------------------------------------------------------------
var QRUtil = (function () {
    var PATTERN_POSITION_TABLE = [
        [],
        [6, 18],
        [6, 22],
        [6, 26],
        [6, 30],
        [6, 34],
        [6, 22, 38],
        [6, 24, 42],
        [6, 26, 46],
        [6, 28, 50],
        [6, 30, 54],
        [6, 32, 58],
        [6, 34, 62],
        [6, 26, 46, 66],
        [6, 26, 48, 70],
        [6, 26, 50, 74],
        [6, 30, 54, 78],
        [6, 30, 56, 82],
        [6, 30, 58, 86],
        [6, 34, 62, 90],
        [6, 28, 50, 72, 94],
        [6, 26, 50, 74, 98],
        [6, 30, 54, 78, 102],
        [6, 28, 54, 80, 106],
        [6, 32, 58, 84, 110],
        [6, 30, 58, 86, 114],
        [6, 34, 62, 90, 118],
        [6, 26, 50, 74, 98, 122],
        [6, 30, 54, 78, 102, 126],
        [6, 26, 52, 78, 104, 130],
        [6, 30, 56, 82, 108, 134],
        [6, 34, 60, 86, 112, 138],
        [6, 30, 58, 86, 114, 142],
        [6, 34, 62, 90, 118, 146],
        [6, 30, 54, 78, 102, 126, 150],
        [6, 24, 50, 76, 102, 128, 154],
        [6, 28, 54, 80, 106, 132, 158],
        [6, 32, 58, 84, 110, 136, 162],
        [6, 26, 54, 82, 110, 138, 166],
        [6, 30, 58, 86, 114, 142, 170]
    ];
    var G15 = (1 << 10) | (1 << 8) | (1 << 5) | (1 << 4) | (1 << 2) | (1 << 1) | (1 << 0);
    var G18 = (1 << 12) |
        (1 << 11) |
        (1 << 10) |
        (1 << 9) |
        (1 << 8) |
        (1 << 5) |
        (1 << 2) |
        (1 << 0);
    var G15_MASK = (1 << 14) | (1 << 12) | (1 << 10) | (1 << 4) | (1 << 1);
    var _this = {};
    var getBCHDigit = function (data) {
        var digit = 0;
        while (data != 0) {
            digit += 1;
            data >>>= 1;
        }
        return digit;
    };
    _this.getBCHTypeInfo = function (data) {
        var d = data << 10;
        while (getBCHDigit(d) - getBCHDigit(G15) >= 0) {
            d ^= G15 << (getBCHDigit(d) - getBCHDigit(G15));
        }
        return ((data << 10) | d) ^ G15_MASK;
    };
    _this.getBCHTypeNumber = function (data) {
        var d = data << 12;
        while (getBCHDigit(d) - getBCHDigit(G18) >= 0) {
            d ^= G18 << (getBCHDigit(d) - getBCHDigit(G18));
        }
        return (data << 12) | d;
    };
    _this.getPatternPosition = function (typeNumber) {
        return PATTERN_POSITION_TABLE[typeNumber - 1];
    };
    _this.getMaskFunction = function (maskPattern) {
        switch (maskPattern) {
            case QRMaskPattern.PATTERN000:
                return function (i, j) {
                    return (i + j) % 2 == 0;
                };
            case QRMaskPattern.PATTERN001:
                return function (i) {
                    return i % 2 == 0;
                };
            case QRMaskPattern.PATTERN010:
                return function (_i, j) {
                    return j % 3 == 0;
                };
            case QRMaskPattern.PATTERN011:
                return function (i, j) {
                    return (i + j) % 3 == 0;
                };
            case QRMaskPattern.PATTERN100:
                return function (i, j) {
                    return (Math.floor(i / 2) + Math.floor(j / 3)) % 2 == 0;
                };
            case QRMaskPattern.PATTERN101:
                return function (i, j) {
                    return ((i * j) % 2) + ((i * j) % 3) == 0;
                };
            case QRMaskPattern.PATTERN110:
                return function (i, j) {
                    return (((i * j) % 2) + ((i * j) % 3)) % 2 == 0;
                };
            case QRMaskPattern.PATTERN111:
                return function (i, j) {
                    return (((i * j) % 3) + ((i + j) % 2)) % 2 == 0;
                };
            default:
                throw new Error('bad maskPattern:' + maskPattern);
        }
    };
    _this.getErrorCorrectPolynomial = function (errorCorrectLength) {
        var a = qrPolynomial([1], 0);
        for (var i = 0; i < errorCorrectLength; i += 1) {
            a = a.multiply(qrPolynomial([1, QRMath.gexp(i)], 0));
        }
        return a;
    };
    _this.getLengthInBits = function (mode, type) {
        if (type >= 1 && type < 10) {
            // 1 - 9
            switch (mode) {
                case QRMode.MODE_NUMBER:
                    return 10;
                case QRMode.MODE_ALPHA_NUM:
                    return 9;
                case QRMode.MODE_8BIT_BYTE:
                    return 8;
                case QRMode.MODE_KANJI:
                    return 8;
                default:
                    throw new Error('mode:' + mode);
            }
        }
        else if (type < 27) {
            // 10 - 26
            switch (mode) {
                case QRMode.MODE_NUMBER:
                    return 12;
                case QRMode.MODE_ALPHA_NUM:
                    return 11;
                case QRMode.MODE_8BIT_BYTE:
                    return 16;
                case QRMode.MODE_KANJI:
                    return 10;
                default:
                    throw new Error('mode:' + mode);
            }
        }
        else if (type < 41) {
            // 27 - 40
            switch (mode) {
                case QRMode.MODE_NUMBER:
                    return 14;
                case QRMode.MODE_ALPHA_NUM:
                    return 13;
                case QRMode.MODE_8BIT_BYTE:
                    return 16;
                case QRMode.MODE_KANJI:
                    return 12;
                default:
                    throw new Error('mode:' + mode);
            }
        }
        else {
            throw new Error('type:' + type);
        }
    };
    _this.getLostPoint = function (qrcode) {
        var moduleCount = qrcode.getModuleCount();
        var lostPoint = 0;
        // LEVEL1
        for (var row = 0; row < moduleCount; row += 1) {
            for (var col = 0; col < moduleCount; col += 1) {
                var sameCount = 0;
                var dark = qrcode.isDark(row, col);
                for (var r = -1; r <= 1; r += 1) {
                    if (row + r < 0 || moduleCount <= row + r) {
                        continue;
                    }
                    for (var c = -1; c <= 1; c += 1) {
                        if (col + c < 0 || moduleCount <= col + c) {
                            continue;
                        }
                        if (r == 0 && c == 0) {
                            continue;
                        }
                        if (dark == qrcode.isDark(row + r, col + c)) {
                            sameCount += 1;
                        }
                    }
                }
                if (sameCount > 5) {
                    lostPoint += 3 + sameCount - 5;
                }
            }
        }
        // LEVEL2
        for (var row = 0; row < moduleCount - 1; row += 1) {
            for (var col = 0; col < moduleCount - 1; col += 1) {
                var count = 0;
                if (qrcode.isDark(row, col))
                    count += 1;
                if (qrcode.isDark(row + 1, col))
                    count += 1;
                if (qrcode.isDark(row, col + 1))
                    count += 1;
                if (qrcode.isDark(row + 1, col + 1))
                    count += 1;
                if (count == 0 || count == 4) {
                    lostPoint += 3;
                }
            }
        }
        // LEVEL3
        for (var row = 0; row < moduleCount; row += 1) {
            for (var col = 0; col < moduleCount - 6; col += 1) {
                if (qrcode.isDark(row, col) &&
                    !qrcode.isDark(row, col + 1) &&
                    qrcode.isDark(row, col + 2) &&
                    qrcode.isDark(row, col + 3) &&
                    qrcode.isDark(row, col + 4) &&
                    !qrcode.isDark(row, col + 5) &&
                    qrcode.isDark(row, col + 6)) {
                    lostPoint += 40;
                }
            }
        }
        for (var col = 0; col < moduleCount; col += 1) {
            for (var row = 0; row < moduleCount - 6; row += 1) {
                if (qrcode.isDark(row, col) &&
                    !qrcode.isDark(row + 1, col) &&
                    qrcode.isDark(row + 2, col) &&
                    qrcode.isDark(row + 3, col) &&
                    qrcode.isDark(row + 4, col) &&
                    !qrcode.isDark(row + 5, col) &&
                    qrcode.isDark(row + 6, col)) {
                    lostPoint += 40;
                }
            }
        }
        // LEVEL4
        var darkCount = 0;
        for (var col = 0; col < moduleCount; col += 1) {
            for (var row = 0; row < moduleCount; row += 1) {
                if (qrcode.isDark(row, col)) {
                    darkCount += 1;
                }
            }
        }
        var ratio = Math.abs((100 * darkCount) / moduleCount / moduleCount - 50) / 5;
        lostPoint += ratio * 10;
        return lostPoint;
    };
    return _this;
})();
// ---------------------------------------------------------------------
// QRMath
// ---------------------------------------------------------------------
var QRMath = (function () {
    var EXP_TABLE = new Array(256);
    var LOG_TABLE = new Array(256);
    // initialize tables
    for (var i = 0; i < 8; i += 1) {
        EXP_TABLE[i] = 1 << i;
    }
    for (var i = 8; i < 256; i += 1) {
        EXP_TABLE[i] =
            EXP_TABLE[i - 4] ^ EXP_TABLE[i - 5] ^ EXP_TABLE[i - 6] ^ EXP_TABLE[i - 8];
    }
    for (var i = 0; i < 255; i += 1) {
        LOG_TABLE[EXP_TABLE[i]] = i;
    }
    var _this = {};
    _this.glog = function (n) {
        if (n < 1) {
            throw new Error('glog(' + n + ')');
        }
        return LOG_TABLE[n];
    };
    _this.gexp = function (n) {
        while (n < 0) {
            n += 255;
        }
        while (n >= 256) {
            n -= 255;
        }
        return EXP_TABLE[n];
    };
    return _this;
})();
// ---------------------------------------------------------------------
// qrPolynomial
// ---------------------------------------------------------------------
function qrPolynomial(num, shift) {
    if (typeof num.length === 'undefined') {
        throw new Error(num.length + '/' + shift);
    }
    var _num = (function () {
        var offset = 0;
        while (offset < num.length && num[offset] == 0) {
            offset += 1;
        }
        var _num = new Array(num.length - offset + shift);
        for (var i = 0; i < num.length - offset; i += 1) {
            _num[i] = num[i + offset];
        }
        return _num;
    })();
    var _this = {};
    _this.getAt = function (index) {
        return _num[index];
    };
    _this.getLength = function () {
        return _num.length;
    };
    _this.multiply = function (e) {
        var num = new Array(_this.getLength() + e.getLength() - 1);
        for (var i = 0; i < _this.getLength(); i += 1) {
            for (var j = 0; j < e.getLength(); j += 1) {
                num[i + j] ^= QRMath.gexp(QRMath.glog(_this.getAt(i)) + QRMath.glog(e.getAt(j)));
            }
        }
        return qrPolynomial(num, 0);
    };
    _this.mod = function (e) {
        if (_this.getLength() - e.getLength() < 0) {
            return _this;
        }
        var ratio = QRMath.glog(_this.getAt(0)) - QRMath.glog(e.getAt(0));
        var num = new Array(_this.getLength());
        for (var i = 0; i < _this.getLength(); i += 1) {
            num[i] = _this.getAt(i);
        }
        for (var i = 0; i < e.getLength(); i += 1) {
            num[i] ^= QRMath.gexp(QRMath.glog(e.getAt(i)) + ratio);
        }
        // recursive call
        return qrPolynomial(num, 0).mod(e);
    };
    return _this;
}
// ---------------------------------------------------------------------
// QRRSBlock
// ---------------------------------------------------------------------
var QRRSBlock = (function () {
    // [1: [L, M, Q, H], ..]
    var RS_BLOCK_TABLE = [
        [1, 26, 19],
        [1, 26, 16],
        [1, 26, 13],
        [1, 26, 9],
        [1, 44, 34],
        [1, 44, 28],
        [1, 44, 22],
        [1, 44, 16],
        [1, 70, 55],
        [1, 70, 44],
        [2, 35, 17],
        [2, 35, 13],
        [1, 100, 80],
        [2, 50, 32],
        [2, 50, 24],
        [4, 25, 9],
        [1, 134, 108],
        [2, 67, 43],
        [2, 33, 15, 2, 34, 16],
        [2, 33, 11, 2, 34, 12],
        [2, 86, 68],
        [4, 43, 27],
        [4, 43, 19],
        [4, 43, 15],
        [2, 98, 78],
        [4, 49, 31],
        [2, 32, 14, 4, 33, 15],
        [4, 39, 13, 1, 40, 14],
        [2, 121, 97],
        [2, 60, 38, 2, 61, 39],
        [4, 40, 18, 2, 41, 19],
        [4, 40, 14, 2, 41, 15],
        [2, 146, 116],
        [3, 58, 36, 2, 59, 37],
        [4, 36, 16, 4, 37, 17],
        [4, 36, 12, 4, 37, 13],
        [2, 86, 68, 2, 87, 69],
        [4, 69, 43, 1, 70, 44],
        [6, 43, 19, 2, 44, 20],
        [6, 43, 15, 2, 44, 16],
        [4, 101, 81],
        [1, 80, 50, 4, 81, 51],
        [4, 50, 22, 4, 51, 23],
        [3, 36, 12, 8, 37, 13],
        [2, 116, 92, 2, 117, 93],
        [6, 58, 36, 2, 59, 37],
        [4, 46, 20, 6, 47, 21],
        [7, 42, 14, 4, 43, 15],
        [4, 133, 107],
        [8, 59, 37, 1, 60, 38],
        [8, 44, 20, 4, 45, 21],
        [12, 33, 11, 4, 34, 12],
        [3, 145, 115, 1, 146, 116],
        [4, 64, 40, 5, 65, 41],
        [11, 36, 16, 5, 37, 17],
        [11, 36, 12, 5, 37, 13],
        [5, 109, 87, 1, 110, 88],
        [5, 65, 41, 5, 66, 42],
        [5, 54, 24, 7, 55, 25],
        [11, 36, 12],
        [5, 122, 98, 1, 123, 99],
        [7, 73, 45, 3, 74, 46],
        [15, 43, 19, 2, 44, 20],
        [3, 45, 15, 13, 46, 16],
        [1, 135, 107, 5, 136, 108],
        [10, 74, 46, 1, 75, 47],
        [1, 50, 22, 15, 51, 23],
        [2, 42, 14, 17, 43, 15],
        [5, 150, 120, 1, 151, 121],
        [9, 69, 43, 4, 70, 44],
        [17, 50, 22, 1, 51, 23],
        [2, 42, 14, 19, 43, 15],
        [3, 141, 113, 4, 142, 114],
        [3, 70, 44, 11, 71, 45],
        [17, 47, 21, 4, 48, 22],
        [9, 39, 13, 16, 40, 14],
        [3, 135, 107, 5, 136, 108],
        [3, 67, 41, 13, 68, 42],
        [15, 54, 24, 5, 55, 25],
        [15, 43, 15, 10, 44, 16],
        [4, 144, 116, 4, 145, 117],
        [17, 68, 42],
        [17, 50, 22, 6, 51, 23],
        [19, 46, 16, 6, 47, 17],
        [2, 139, 111, 7, 140, 112],
        [17, 74, 46],
        [7, 54, 24, 16, 55, 25],
        [34, 37, 13],
        [4, 151, 121, 5, 152, 122],
        [4, 75, 47, 14, 76, 48],
        [11, 54, 24, 14, 55, 25],
        [16, 45, 15, 14, 46, 16],
        [6, 147, 117, 4, 148, 118],
        [6, 73, 45, 14, 74, 46],
        [11, 54, 24, 16, 55, 25],
        [30, 46, 16, 2, 47, 17],
        [8, 132, 106, 4, 133, 107],
        [8, 75, 47, 13, 76, 48],
        [7, 54, 24, 22, 55, 25],
        [22, 45, 15, 13, 46, 16],
        [10, 142, 114, 2, 143, 115],
        [19, 74, 46, 4, 75, 47],
        [28, 50, 22, 6, 51, 23],
        [33, 46, 16, 4, 47, 17],
        [8, 152, 122, 4, 153, 123],
        [22, 73, 45, 3, 74, 46],
        [8, 53, 23, 26, 54, 24],
        [12, 45, 15, 28, 46, 16],
        [3, 147, 117, 10, 148, 118],
        [3, 73, 45, 23, 74, 46],
        [4, 54, 24, 31, 55, 25],
        [11, 45, 15, 31, 46, 16],
        [7, 146, 116, 7, 147, 117],
        [21, 73, 45, 7, 74, 46],
        [1, 53, 23, 37, 54, 24],
        [19, 45, 15, 26, 46, 16],
        [5, 145, 115, 10, 146, 116],
        [19, 75, 47, 10, 76, 48],
        [15, 54, 24, 25, 55, 25],
        [23, 45, 15, 25, 46, 16],
        [13, 145, 115, 3, 146, 116],
        [2, 74, 46, 29, 75, 47],
        [42, 54, 24, 1, 55, 25],
        [23, 45, 15, 28, 46, 16],
        [17, 145, 115],
        [10, 74, 46, 23, 75, 47],
        [10, 54, 24, 35, 55, 25],
        [19, 45, 15, 35, 46, 16],
        [17, 145, 115, 1, 146, 116],
        [14, 74, 46, 21, 75, 47],
        [29, 54, 24, 19, 55, 25],
        [11, 45, 15, 46, 46, 16],
        [13, 145, 115, 6, 146, 116],
        [14, 74, 46, 23, 75, 47],
        [44, 54, 24, 7, 55, 25],
        [59, 46, 16, 1, 47, 17],
        [12, 151, 121, 7, 152, 122],
        [12, 75, 47, 26, 76, 48],
        [39, 54, 24, 14, 55, 25],
        [22, 45, 15, 41, 46, 16],
        [6, 151, 121, 14, 152, 122],
        [6, 75, 47, 34, 76, 48],
        [46, 54, 24, 10, 55, 25],
        [2, 45, 15, 64, 46, 16],
        [17, 152, 122, 4, 153, 123],
        [29, 74, 46, 14, 75, 47],
        [49, 54, 24, 10, 55, 25],
        [24, 45, 15, 46, 46, 16],
        [4, 152, 122, 18, 153, 123],
        [13, 74, 46, 32, 75, 47],
        [48, 54, 24, 14, 55, 25],
        [42, 45, 15, 32, 46, 16],
        [20, 147, 117, 4, 148, 118],
        [40, 75, 47, 7, 76, 48],
        [43, 54, 24, 22, 55, 25],
        [10, 45, 15, 67, 46, 16],
        [19, 148, 118, 6, 149, 119],
        [18, 75, 47, 31, 76, 48],
        [34, 54, 24, 34, 55, 25],
        [20, 45, 15, 61, 46, 16]
    ];
    var qrRSBlock = function (totalCount, dataCount) {
        var _this = {};
        _this.totalCount = totalCount;
        _this.dataCount = dataCount;
        return _this;
    };
    var _this = {};
    var getRsBlockTable = function (typeNumber, errorCorrectLevel) {
        switch (errorCorrectLevel) {
            case QRErrorCorrectLevel.L:
                return RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 0];
            case QRErrorCorrectLevel.M:
                return RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 1];
            case QRErrorCorrectLevel.Q:
                return RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 2];
            case QRErrorCorrectLevel.H:
                return RS_BLOCK_TABLE[(typeNumber - 1) * 4 + 3];
            default:
                return undefined;
        }
    };
    _this.getRSBlocks = function (typeNumber, errorCorrectLevel) {
        var rsBlock = getRsBlockTable(typeNumber, errorCorrectLevel);
        if (typeof rsBlock === 'undefined') {
            throw new Error('bad rs block @ typeNumber:' +
                typeNumber +
                '/errorCorrectLevel:' +
                errorCorrectLevel);
        }
        var length = rsBlock.length / 3;
        var list = [];
        for (var i = 0; i < length; i += 1) {
            var count = rsBlock[i * 3 + 0];
            var totalCount = rsBlock[i * 3 + 1];
            var dataCount = rsBlock[i * 3 + 2];
            for (var j = 0; j < count; j += 1) {
                list.push(qrRSBlock(totalCount, dataCount));
            }
        }
        return list;
    };
    return _this;
})();
// ---------------------------------------------------------------------
// qrBitBuffer
// ---------------------------------------------------------------------
var qrBitBuffer = function () {
    var _buffer = [];
    var _length = 0;
    var _this = {};
    _this.getBuffer = function () {
        return _buffer;
    };
    _this.getAt = function (index) {
        var bufIndex = Math.floor(index / 8);
        return ((_buffer[bufIndex] >>> (7 - (index % 8))) & 1) == 1;
    };
    _this.put = function (num, length) {
        for (var i = 0; i < length; i += 1) {
            _this.putBit(((num >>> (length - i - 1)) & 1) == 1);
        }
    };
    _this.getLengthInBits = function () {
        return _length;
    };
    _this.putBit = function (bit) {
        var bufIndex = Math.floor(_length / 8);
        if (_buffer.length <= bufIndex) {
            _buffer.push(0);
        }
        if (bit) {
            _buffer[bufIndex] |= 0x80 >>> _length % 8;
        }
        _length += 1;
    };
    return _this;
};
// ---------------------------------------------------------------------
// qr8BitByte
// ---------------------------------------------------------------------
var qr8BitByte = function (data) {
    var _mode = QRMode.MODE_8BIT_BYTE;
    var _data = data;
    var _parsedData = [];
    var _this = {};
    // Added to support UTF-8 Characters
    for (var i = 0, l = _data.length; i < l; i++) {
        var byteArray = [];
        var code = _data.charCodeAt(i);
        if (code > 0x10000) {
            byteArray[0] = 0xf0 | ((code & 0x1c0000) >>> 18);
            byteArray[1] = 0x80 | ((code & 0x3f000) >>> 12);
            byteArray[2] = 0x80 | ((code & 0xfc0) >>> 6);
            byteArray[3] = 0x80 | (code & 0x3f);
        }
        else if (code > 0x800) {
            byteArray[0] = 0xe0 | ((code & 0xf000) >>> 12);
            byteArray[1] = 0x80 | ((code & 0xfc0) >>> 6);
            byteArray[2] = 0x80 | (code & 0x3f);
        }
        else if (code > 0x80) {
            byteArray[0] = 0xc0 | ((code & 0x7c0) >>> 6);
            byteArray[1] = 0x80 | (code & 0x3f);
        }
        else {
            byteArray[0] = code;
        }
        // Fix Unicode corruption bug
        _parsedData.push(byteArray);
    }
    _parsedData = Array.prototype.concat.apply([], _parsedData);
    if (_parsedData.length != _data.length) {
        _parsedData.unshift(191);
        _parsedData.unshift(187);
        _parsedData.unshift(239);
    }
    var _bytes = _parsedData;
    _this.getMode = function () {
        return _mode;
    };
    _this.getLength = function () {
        return _bytes.length;
    };
    _this.write = function (buffer) {
        for (var i = 0; i < _bytes.length; i += 1) {
            buffer.put(_bytes[i], 8);
        }
    };
    return _this;
};
//= ====================================================================
// GIF Support etc.
//
// ---------------------------------------------------------------------
// byteArrayOutputStream
// ---------------------------------------------------------------------
var byteArrayOutputStream = function () {
    var _bytes = [];
    var _this = {};
    _this.writeByte = function (b) {
        _bytes.push(b & 0xff);
    };
    _this.writeShort = function (i) {
        _this.writeByte(i);
        _this.writeByte(i >>> 8);
    };
    _this.writeBytes = function (b, off, len) {
        off = off || 0;
        len = len || b.length;
        for (var i = 0; i < len; i += 1) {
            _this.writeByte(b[i + off]);
        }
    };
    _this.writeString = function (s) {
        for (var i = 0; i < s.length; i += 1) {
            _this.writeByte(s.charCodeAt(i));
        }
    };
    _this.toByteArray = function () {
        return _bytes;
    };
    _this.toString = function () {
        var s = '';
        s += '[';
        for (var i = 0; i < _bytes.length; i += 1) {
            if (i > 0) {
                s += ',';
            }
            s += _bytes[i];
        }
        s += ']';
        return s;
    };
    return _this;
};
// ---------------------------------------------------------------------
// base64EncodeOutputStream
// ---------------------------------------------------------------------
var base64EncodeOutputStream = function () {
    var _buffer = 0;
    var _buflen = 0;
    var _length = 0;
    var _base64 = '';
    var _this = {};
    var writeEncoded = function (b) {
        _base64 += String.fromCharCode(encode(b & 0x3f));
    };
    var encode = function (n) {
        if (n < 0) ;
        else if (n < 26) {
            return 0x41 + n;
        }
        else if (n < 52) {
            return 0x61 + (n - 26);
        }
        else if (n < 62) {
            return 0x30 + (n - 52);
        }
        else if (n == 62) {
            return 0x2b;
        }
        else if (n == 63) {
            return 0x2f;
        }
        throw new Error('n:' + n);
    };
    _this.writeByte = function (n) {
        _buffer = (_buffer << 8) | (n & 0xff);
        _buflen += 8;
        _length += 1;
        while (_buflen >= 6) {
            writeEncoded(_buffer >>> (_buflen - 6));
            _buflen -= 6;
        }
    };
    _this.flush = function () {
        if (_buflen > 0) {
            writeEncoded(_buffer << (6 - _buflen));
            _buffer = 0;
            _buflen = 0;
        }
        if (_length % 3 != 0) {
            // padding
            var padlen = 3 - (_length % 3);
            for (var i = 0; i < padlen; i += 1) {
                _base64 += '=';
            }
        }
    };
    _this.toString = function () {
        return _base64;
    };
    return _this;
};
// ---------------------------------------------------------------------
// base64DecodeInputStream
// ---------------------------------------------------------------------
var base64DecodeInputStream = function (str) {
    var _str = str;
    var _pos = 0;
    var _buffer = 0;
    var _buflen = 0;
    var _this = {};
    _this.read = function () {
        while (_buflen < 8) {
            if (_pos >= _str.length) {
                if (_buflen == 0) {
                    return -1;
                }
                throw new Error('unexpected end of file./' + _buflen);
            }
            var c = _str.charAt(_pos);
            _pos += 1;
            if (c == '=') {
                _buflen = 0;
                return -1;
            }
            else if (c.match(/^\s$/)) {
                // ignore if whitespace.
                continue;
            }
            _buffer = (_buffer << 6) | decode(c.charCodeAt(0));
            _buflen += 6;
        }
        var n = (_buffer >>> (_buflen - 8)) & 0xff;
        _buflen -= 8;
        return n;
    };
    var decode = function (c) {
        if (c >= 0x41 && c <= 0x5a) {
            return c - 0x41;
        }
        else if (c >= 0x61 && c <= 0x7a) {
            return c - 0x61 + 26;
        }
        else if (c >= 0x30 && c <= 0x39) {
            return c - 0x30 + 52;
        }
        else if (c == 0x2b) {
            return 62;
        }
        else if (c == 0x2f) {
            return 63;
        }
        else {
            throw new Error('c:' + c);
        }
    };
    return _this;
};
// ---------------------------------------------------------------------
// gifImage (B/W)
// ---------------------------------------------------------------------
var gifImage = function (width, height) {
    var _width = width;
    var _height = height;
    var _data = new Array(width * height);
    var _this = {};
    _this.setPixel = function (x, y, pixel) {
        _data[y * _width + x] = pixel;
    };
    _this.write = function (out) {
        // ---------------------------------
        // GIF Signature
        out.writeString('GIF87a');
        // ---------------------------------
        // Screen Descriptor
        out.writeShort(_width);
        out.writeShort(_height);
        out.writeByte(0x80); // 2bit
        out.writeByte(0);
        out.writeByte(0);
        // ---------------------------------
        // Global Color Map
        // black
        out.writeByte(0x00);
        out.writeByte(0x00);
        out.writeByte(0x00);
        // white
        out.writeByte(0xff);
        out.writeByte(0xff);
        out.writeByte(0xff);
        // ---------------------------------
        // Image Descriptor
        out.writeString(',');
        out.writeShort(0);
        out.writeShort(0);
        out.writeShort(_width);
        out.writeShort(_height);
        out.writeByte(0);
        // ---------------------------------
        // Local Color Map
        // ---------------------------------
        // Raster Data
        var lzwMinCodeSize = 2;
        var raster = getLZWRaster(lzwMinCodeSize);
        out.writeByte(lzwMinCodeSize);
        var offset = 0;
        while (raster.length - offset > 255) {
            out.writeByte(255);
            out.writeBytes(raster, offset, 255);
            offset += 255;
        }
        out.writeByte(raster.length - offset);
        out.writeBytes(raster, offset, raster.length - offset);
        out.writeByte(0x00);
        // ---------------------------------
        // GIF Terminator
        out.writeString(';');
    };
    var bitOutputStream = function (out) {
        var _out = out;
        var _bitLength = 0;
        var _bitBuffer = 0;
        var _this = {};
        _this.write = function (data, length) {
            if (data >>> length != 0) {
                throw new Error('length over');
            }
            while (_bitLength + length >= 8) {
                _out.writeByte(0xff & ((data << _bitLength) | _bitBuffer));
                length -= 8 - _bitLength;
                data >>>= 8 - _bitLength;
                _bitBuffer = 0;
                _bitLength = 0;
            }
            _bitBuffer = (data << _bitLength) | _bitBuffer;
            _bitLength = _bitLength + length;
        };
        _this.flush = function () {
            if (_bitLength > 0) {
                _out.writeByte(_bitBuffer);
            }
        };
        return _this;
    };
    var getLZWRaster = function (lzwMinCodeSize) {
        var clearCode = 1 << lzwMinCodeSize;
        var endCode = (1 << lzwMinCodeSize) + 1;
        var bitLength = lzwMinCodeSize + 1;
        // Setup LZWTable
        var table = lzwTable();
        for (var i = 0; i < clearCode; i += 1) {
            table.add(String.fromCharCode(i));
        }
        table.add(String.fromCharCode(clearCode));
        table.add(String.fromCharCode(endCode));
        var byteOut = byteArrayOutputStream();
        var bitOut = bitOutputStream(byteOut);
        // clear code
        bitOut.write(clearCode, bitLength);
        var dataIndex = 0;
        var s = String.fromCharCode(_data[dataIndex]);
        dataIndex += 1;
        while (dataIndex < _data.length) {
            var c = String.fromCharCode(_data[dataIndex]);
            dataIndex += 1;
            if (table.contains(s + c)) {
                s = s + c;
            }
            else {
                bitOut.write(table.indexOf(s), bitLength);
                if (table.size() < 0xfff) {
                    if (table.size() == 1 << bitLength) {
                        bitLength += 1;
                    }
                    table.add(s + c);
                }
                s = c;
            }
        }
        bitOut.write(table.indexOf(s), bitLength);
        // end code
        bitOut.write(endCode, bitLength);
        bitOut.flush();
        return byteOut.toByteArray();
    };
    var lzwTable = function () {
        var _map = {};
        var _size = 0;
        var _this = {};
        _this.add = function (key) {
            if (_this.contains(key)) {
                throw new Error('dup key:' + key);
            }
            _map[key] = _size;
            _size += 1;
        };
        _this.size = function () {
            return _size;
        };
        _this.indexOf = function (key) {
            return _map[key];
        };
        _this.contains = function (key) {
            return typeof _map[key] !== 'undefined';
        };
        return _this;
    };
    return _this;
};
var createImgTag = function (width, height, getPixel) {
    var gif = gifImage(width, height);
    for (var y = 0; y < height; y += 1) {
        for (var x = 0; x < width; x += 1) {
            gif.setPixel(x, y, getPixel(x, y));
        }
    }
    var b = byteArrayOutputStream();
    gif.write(b);
    var base64 = base64EncodeOutputStream();
    var bytes = b.toByteArray();
    for (var i = 0; i < bytes.length; i += 1) {
        base64.writeByte(bytes[i]);
    }
    base64.flush();
    var img = '';
    img += 'data:image/gif;base64,';
    img += base64;
    return img;
};
// ---------------------------------------------------------------------
// returns qrcode function.
// eslint-disable-next-line import/prefer-default-export
var createQrCodeImg = function (text, options) {
    options = options || {};
    var typeNumber = options.typeNumber || 4;
    var errorCorrectLevel = options.errorCorrectLevel || 'M';
    var size = options.size || 500;
    var qr;
    try {
        qr = qrcode(typeNumber, errorCorrectLevel || 'M');
        qr.addData(text);
        qr.make();
    }
    catch (e) {
        if (typeNumber >= 40) {
            throw new Error('Text too long to encode');
        }
        else {
            return createQrCodeImg(text, {
                size: size,
                errorCorrectLevel: errorCorrectLevel,
                typeNumber: typeNumber + 1
            });
        }
    }
    // calc cellsize and margin
    var cellsize = parseInt("" + size / qr.getModuleCount());
    var margin = parseInt("" + (size - qr.getModuleCount() * cellsize) / 2);
    return qr.createImgTag(cellsize, margin, size);
};

var QRCode = function (_a) {
    var _b = _a.text, text = _b === void 0 ? '' : _b, _c = _a.size, size = _c === void 0 ? 100 : _c, _d = _a.scale, scale = _d === void 0 ? 4 : _d, _e = _a.typeNumber, typeNumber = _e === void 0 ? 2 : _e, _f = _a.errorCorrectLevel, errorCorrectLevel = _f === void 0 ? 'M' : _f, _g = _a.style, style = _g === void 0 ? {} : _g;
    var image = useMemo(function () {
        var options = { errorCorrectLevel: errorCorrectLevel, typeNumber: typeNumber, size: size * scale };
        return createQrCodeImg(text, options);
    }, [text, scale, size, errorCorrectLevel, typeNumber]);
    var widthString = size ? size + 'px' : '';
    var heightString = size ? size + 'px' : '';
    var finalStyle = __assign({ width: widthString, height: heightString }, style);
    return React.createElement(Image, { style: finalStyle, src: image });
};
QRCode.propTypes = {
    text: propTypes.string.isRequired,
    size: propTypes.number,
    scale: propTypes.number,
    style: propTypes.object,
    errorCorrectLevel: propTypes.string,
    typeNumber: propTypes.number
};

export { Barcode, QRCode };
//# sourceMappingURL=index.esm.js.map
