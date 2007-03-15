/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class AConditionalExpr extends PExpr
{
    private TLParenthese _lParenthese_;
    private POrExpr _if_;
    private TRightarrow _rightarrow_;
    private POrExpr _then_;
    private TColon _colon_;
    private POrExpr _else_;
    private TRParenthese _rParenthese_;

    public AConditionalExpr()
    {
        // Constructor
    }

    public AConditionalExpr(
        @SuppressWarnings("hiding") TLParenthese _lParenthese_,
        @SuppressWarnings("hiding") POrExpr _if_,
        @SuppressWarnings("hiding") TRightarrow _rightarrow_,
        @SuppressWarnings("hiding") POrExpr _then_,
        @SuppressWarnings("hiding") TColon _colon_,
        @SuppressWarnings("hiding") POrExpr _else_,
        @SuppressWarnings("hiding") TRParenthese _rParenthese_)
    {
        // Constructor
        setLParenthese(_lParenthese_);

        setIf(_if_);

        setRightarrow(_rightarrow_);

        setThen(_then_);

        setColon(_colon_);

        setElse(_else_);

        setRParenthese(_rParenthese_);

    }

    @Override
    public Object clone()
    {
        return new AConditionalExpr(
            cloneNode(this._lParenthese_),
            cloneNode(this._if_),
            cloneNode(this._rightarrow_),
            cloneNode(this._then_),
            cloneNode(this._colon_),
            cloneNode(this._else_),
            cloneNode(this._rParenthese_));
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseAConditionalExpr(this);
    }

    public TLParenthese getLParenthese()
    {
        return this._lParenthese_;
    }

    public void setLParenthese(TLParenthese node)
    {
        if(this._lParenthese_ != null)
        {
            this._lParenthese_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._lParenthese_ = node;
    }

    public POrExpr getIf()
    {
        return this._if_;
    }

    public void setIf(POrExpr node)
    {
        if(this._if_ != null)
        {
            this._if_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._if_ = node;
    }

    public TRightarrow getRightarrow()
    {
        return this._rightarrow_;
    }

    public void setRightarrow(TRightarrow node)
    {
        if(this._rightarrow_ != null)
        {
            this._rightarrow_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._rightarrow_ = node;
    }

    public POrExpr getThen()
    {
        return this._then_;
    }

    public void setThen(POrExpr node)
    {
        if(this._then_ != null)
        {
            this._then_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._then_ = node;
    }

    public TColon getColon()
    {
        return this._colon_;
    }

    public void setColon(TColon node)
    {
        if(this._colon_ != null)
        {
            this._colon_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._colon_ = node;
    }

    public POrExpr getElse()
    {
        return this._else_;
    }

    public void setElse(POrExpr node)
    {
        if(this._else_ != null)
        {
            this._else_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._else_ = node;
    }

    public TRParenthese getRParenthese()
    {
        return this._rParenthese_;
    }

    public void setRParenthese(TRParenthese node)
    {
        if(this._rParenthese_ != null)
        {
            this._rParenthese_.parent(null);
        }

        if(node != null)
        {
            if(node.parent() != null)
            {
                node.parent().removeChild(node);
            }

            node.parent(this);
        }

        this._rParenthese_ = node;
    }

    @Override
    public String toString()
    {
        return ""
            + toString(this._lParenthese_)
            + toString(this._if_)
            + toString(this._rightarrow_)
            + toString(this._then_)
            + toString(this._colon_)
            + toString(this._else_)
            + toString(this._rParenthese_);
    }

    @Override
    void removeChild(@SuppressWarnings("unused") Node child)
    {
        // Remove child
        if(this._lParenthese_ == child)
        {
            this._lParenthese_ = null;
            return;
        }

        if(this._if_ == child)
        {
            this._if_ = null;
            return;
        }

        if(this._rightarrow_ == child)
        {
            this._rightarrow_ = null;
            return;
        }

        if(this._then_ == child)
        {
            this._then_ = null;
            return;
        }

        if(this._colon_ == child)
        {
            this._colon_ = null;
            return;
        }

        if(this._else_ == child)
        {
            this._else_ = null;
            return;
        }

        if(this._rParenthese_ == child)
        {
            this._rParenthese_ = null;
            return;
        }

        throw new RuntimeException("Not a child.");
    }

    @Override
    void replaceChild(@SuppressWarnings("unused") Node oldChild, @SuppressWarnings("unused") Node newChild)
    {
        // Replace child
        if(this._lParenthese_ == oldChild)
        {
            setLParenthese((TLParenthese) newChild);
            return;
        }

        if(this._if_ == oldChild)
        {
            setIf((POrExpr) newChild);
            return;
        }

        if(this._rightarrow_ == oldChild)
        {
            setRightarrow((TRightarrow) newChild);
            return;
        }

        if(this._then_ == oldChild)
        {
            setThen((POrExpr) newChild);
            return;
        }

        if(this._colon_ == oldChild)
        {
            setColon((TColon) newChild);
            return;
        }

        if(this._else_ == oldChild)
        {
            setElse((POrExpr) newChild);
            return;
        }

        if(this._rParenthese_ == oldChild)
        {
            setRParenthese((TRParenthese) newChild);
            return;
        }

        throw new RuntimeException("Not a child.");
    }
}
