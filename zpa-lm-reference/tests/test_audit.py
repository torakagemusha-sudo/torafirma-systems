from __future__ import annotations

from zpa_lm_reference.audit import run_audit


def test_audit_contract() -> None:
    result = run_audit(limit=24)
    assert result["keystone"]["max_abs_error_closed_form_vs_direct_bc"] <= 1e-15
    assert result["keystone"]["max_abs_error_closed_form_vs_exponent_product"] <= 2e-15
    assert result["router"]["trainable_parameter_count"] == 0
    assert result["router"]["causal_upper_triangle_max_abs"] == 0.0
    assert result["router"]["causal_row_sum_max_abs_error"] <= 1e-14
    assert result["model"]["query_key_trainable"] == 0
    assert result["model"]["gradient_parameter_count"] > 0
