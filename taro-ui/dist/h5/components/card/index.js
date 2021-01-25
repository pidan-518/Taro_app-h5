import Taro from "@tarojs/taro-h5";
import Nerv from "nervjs";
import classNames from 'classnames';
import PropTypes from 'prop-types';
import { Image, Text, View } from '@tarojs/components';
import AtComponent from '../../common/component';
export default class AtCard extends AtComponent {
  constructor() {
    super(...arguments);
  }
  render() {
    const { title, note, extra, extraStyle, thumb, isFull, icon, renderIcon } = this.props;
    const rootClass = classNames('at-card', {
      'at-card--full': isFull
    }, this.props.className);
    const iconClass = classNames({
      'at-icon': true,
      [`at-icon-${icon && icon.value}`]: icon && icon.value,
      'at-card__header-icon': true
    });
    const iconStyle = {
      color: icon && icon.color || '',
      fontSize: icon && `${icon.size}px` || ''
    };
    return <View onClick={this.handleClick} className={rootClass}>
        <View className="at-card__header">
          {thumb && <View className="at-card__header-thumb">
              <Image className="at-card__header-thumb-info" mode="scaleToFill" src={thumb} />
            </View>}
          {renderIcon || ''}
          {!thumb && icon && icon.value && <Text className={iconClass} style={iconStyle}></Text>}

          <Text className="at-card__header-title">{title}</Text>
          {extra && <Text style={{ ...extraStyle }} className="at-card__header-extra">
              {extra}
            </Text>}
        </View>
        <View className="at-card__content">
          <View className="at-card__content-info">{this.props.children}</View>
          {note && <View className="at-card__content-note">{note}</View>}
        </View>
      </View>;
  }
  handleClick = args => {
    if (typeof this.props.onClick === 'function') {
      this.props.onClick(args);
    }
  };
}
AtCard.defaultProps = {
  note: '',
  isFull: false,
  thumb: '',
  title: '',
  extra: '',
  icon: undefined,
  onClick() {},
  renderIcon: undefined,
  extraStyle: {}
};
AtCard.propTypes = {
  note: PropTypes.string,
  isFull: PropTypes.bool,
  thumb: PropTypes.string,
  title: PropTypes.string,
  extra: PropTypes.string,
  icon: PropTypes.object,
  onClick: PropTypes.func,
  renderIcon: PropTypes.oneOfType([PropTypes.string, PropTypes.element]),
  extraStyle: PropTypes.object // 自定义extra样式
};