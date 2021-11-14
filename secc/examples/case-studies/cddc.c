#include "secc.h"

enum Button {
	ButtonLow, ButtonHigh, ButtonOverlay
};

enum Domain {
	DomainLow, DomainHigh, DomainOverlay, DomainInvalid
};

enum EventType {
	EventTypeMouse, EventTypeNone, EventTypeKeyboard
};

enum Event {
	EventNone, EventMouseDown
};

typedef enum Button Button;
typedef enum Domain Domain;
typedef enum EventType EventType;
typedef enum Event Event;

void lock_rpc_overlay_mouse_click();
  _(ensures exists int call, Button button, Domain domain.
    call :: low && button :: low && domain :: low &&
    rpc_overlay_mouse_click_call |->[low] call &&
    rpc_overlay_mouse_click_arg  |->[low] button &&
    rpc_overlay_mouse_click_ret  |->[low] domain)

void unlock_rpc_overlay_mouse_click();
  _(requires exists int call, Button button, Domain domain.
    call :: low && button :: low && domain :: low &&
    rpc_overlay_mouse_click_call |->[low] call &&
    rpc_overlay_mouse_click_arg  |->[low] button &&
    rpc_overlay_mouse_click_ret  |->[low] domain)

void lock_hid_read_atomicity();
  _(ensures exists Button button, int mouse, int keyboard, Event high_key, Event low_key.
    mouse :: low && button :: low && keyboard :: low && low_key :: low &&
    hid_mouse_available      |->[low]  mouse &&
    hid_mouse_source         |->[low]  button &&
    hid_keyboard_available   |->[low]  keyboard &&
    hid_high_keyboard_source |->[high] high_key &&
    hid_low_keyboard_source  |->[low]  low_key)

void unlock_hid_read_atomicity();
  _(requires exists Button button, int mouse, int keyboard, Event high_key, Event low_key.
    mouse :: low && button :: low && keyboard :: low && low_key :: low &&
    hid_mouse_available      |->[low]  mouse &&
    hid_mouse_source         |->[low]  button &&
    hid_keyboard_available   |->[low]  keyboard &&
    hid_high_keyboard_source |->[high] high_key &&
    hid_low_keyboard_source  |->[low]  low_key)

void lock_compositor_read_atomicity();
  _(ensures exists Domain domain.
  compositor_domain_under_cursor |->[low] domain && domain :: low)
  
void unlock_compositor_read_atomicity();
  _(requires exists Domain domain.
  compositor_domain_under_cursor |->[low] domain && domain :: low)

int *rpc_overlay_mouse_click_call;
Button *rpc_overlay_mouse_click_arg;
Domain *rpc_overlay_mouse_click_ret;

int *hid_mouse_available;
int *hid_keyboard_available;
EventType *hid_current_event_type;

Button *hid_mouse_source;
Event *hid_low_keyboard_source;
Event *hid_high_keyboard_source;

Event *current_event_data;
Event *output_event_buffer0;
Event *output_event_buffer1;
Domain *active_domain;
Domain *indicated_domain;

Event *compositor_cursor_position;
Domain *compositor_domain_under_cursor;

void driver() {
	while (1) {
		lock_rpc_overlay_mouse_click();

		if (*rpc_overlay_mouse_click_call) {
			*rpc_overlay_mouse_click_call = 0;

			if (*rpc_overlay_mouse_click_arg == ButtonLow) {
				*rpc_overlay_mouse_click_ret = DomainLow;
			} else if (*rpc_overlay_mouse_click_arg == ButtonHigh) {
				*rpc_overlay_mouse_click_ret = DomainHigh;
			} else if (*rpc_overlay_mouse_click_arg == ButtonOverlay) {
				*rpc_overlay_mouse_click_ret = DomainOverlay;
			} else {
				*rpc_overlay_mouse_click_ret = DomainInvalid;
			}
		}

		unlock_rpc_overlay_mouse_click();
	}
}

void input_switch()
  _(maintains exists Domain id, Domain ad, EventType event_type, Event out0, Event out1, Event event, Event event_data.
  active_domain |->[low] ad &&
  indicated_domain |->[low] id &&
  hid_current_event_type |->[low] event_type &&
  output_event_buffer0 |->[low] out0 &&
  output_event_buffer1 |->[high] out1 &&
  compositor_cursor_position |-> [high] event &&
  current_event_data |->[high] event_data)
{
	int temp = 0;
	int done_rpc = 0;
	int switch_state_mouse_down = 0;
	Domain overlay_result = DomainInvalid;
	Domain cursor_domain = DomainInvalid;

	*current_event_data = EventNone;
	*indicated_domain = *active_domain;

	*hid_current_event_type = EventTypeNone;

	while (1)
	  _(invariant exists Domain domain, EventType event_type, Event out0, Event out1, Event event, Event event_data.
	  overlay_result :: low &&
	  // cursor_domain :: low &&
	  event_data :: low &&
	  switch_state_mouse_down :: low &&
	  active_domain |->[low] domain &&
	  indicated_domain |->[low] domain &&
	  hid_current_event_type |->[low] event_type &&
	  output_event_buffer0 |->[low] out0 &&
	  output_event_buffer1 |->[high] out1 &&
	  compositor_cursor_position |-> [high] event &&
	  current_event_data |->[high] event_data)
	{
		lock_hid_read_atomicity();
		temp = *hid_mouse_available;
		unlock_hid_read_atomicity();

		if (temp) {
			*hid_current_event_type = EventTypeMouse;

			lock_hid_read_atomicity();
			Button source = *hid_mouse_source;
			unlock_hid_read_atomicity();

			lock_rpc_overlay_mouse_click();
			*rpc_overlay_mouse_click_arg = source;
			*rpc_overlay_mouse_click_call = 1;
			unlock_rpc_overlay_mouse_click();

			done_rpc = 0;
			while (!done_rpc)
				_(invariant 
					done_rpc :: low &&
					overlay_result :: low)
			{
				lock_rpc_overlay_mouse_click();
				if (!*rpc_overlay_mouse_click_call) {
					overlay_result = *rpc_overlay_mouse_click_ret;
					done_rpc = 1;
				}
				unlock_rpc_overlay_mouse_click();
			}

			if (overlay_result != DomainInvalid) {
				cursor_domain = DomainOverlay;
			} else {
				*compositor_cursor_position = *current_event_data;

				lock_compositor_read_atomicity();
				cursor_domain = *compositor_domain_under_cursor;
				unlock_compositor_read_atomicity();

				if (cursor_domain == DomainInvalid) {
					cursor_domain = *active_domain;
				}
			}

			if (cursor_domain == DomainOverlay) {
				if (overlay_result != DomainOverlay
						&& overlay_result != DomainInvalid
						&& *current_event_data == EventMouseDown
						&& !switch_state_mouse_down
						&& overlay_result != *active_domain) {
					*active_domain = overlay_result;
					*indicated_domain = *active_domain;
				}
			} else {
				if (*current_event_data == EventMouseDown
						&& !switch_state_mouse_down
						&& cursor_domain != *active_domain) {
					*active_domain = cursor_domain;
					*indicated_domain = *active_domain;
				}

				if (switch_state_mouse_down
						|| *current_event_data == EventMouseDown) {
					if (*active_domain == DomainLow) {
						*output_event_buffer0 = *current_event_data;
					} else {
						*output_event_buffer1 = *current_event_data;
					}
				} else {
					if (cursor_domain == DomainLow) {
						*output_event_buffer0 = *current_event_data;
					} else {
						*output_event_buffer1 = *current_event_data;
					}
				}
			}

			if (*current_event_data == EventMouseDown) {
				switch_state_mouse_down = 1;
			} else {
				switch_state_mouse_down = 0;
			}
		}

		lock_hid_read_atomicity();
		temp = *hid_keyboard_available;
		unlock_hid_read_atomicity();

		if (temp) {
			*current_event_data = EventNone;
			*hid_current_event_type = EventTypeKeyboard;

			if (*indicated_domain == DomainHigh) {
				lock_hid_read_atomicity();
				*current_event_data = *hid_high_keyboard_source;
				unlock_hid_read_atomicity();
			} else {
				lock_hid_read_atomicity();
				*current_event_data = *hid_low_keyboard_source;
				unlock_hid_read_atomicity();
			}

			if (*active_domain == DomainLow) {
				*output_event_buffer0 = *current_event_data;
			} else {
				*output_event_buffer1 = *current_event_data;
			}
		}

		*current_event_data = EventNone;
		*hid_current_event_type = EventTypeNone;
	}
}

